const http=require('http'),fs=require('fs'),crypto=require('crypto');
const {WebSocketServer}=require('ws');
const E=process.env,TOKEN=E.BOT_TOKEN||'',ADMIN=String(E.ADMIN_ID||''),DEV=E.DEV==='1',APP=E.APP_URL||'',BOT=E.BOT_USER||'';
let users={};try{users=JSON.parse(fs.readFileSync('db.json'))}catch{}
if(ADMIN&&!users[ADMIN])users[ADMIN]={name:'Админ',chips:0};
const save=()=>fs.writeFileSync('db.json',JSON.stringify(users));
const tables={};let tid=1;const conns=new Set();
const act=t=>t.seats.filter(s=>s.in&&!s.folded);
const pot=t=>t.phase==='azi'?t.carry:t.carry+t.seats.reduce((a,s)=>a+(s.in?s.paid:0),0);

function auth(init){
  if(!init)return null;
  const p=new URLSearchParams(init),h=p.get('hash');p.delete('hash');
  const s=[...p.entries()].map(([k,v])=>k+'='+v).sort().join('\n');
  const key=crypto.createHmac('sha256','WebAppData').update(TOKEN).digest();
  if(crypto.createHmac('sha256',key).update(s).digest('hex')!==h)return null;
  const u=JSON.parse(p.get('user'));return{id:String(u.id),name:u.first_name||u.username||'Игрок'};
}
function pay(t,s,n){const d=Math.max(0,Math.min(n,users[s.id].chips));users[s.id].chips-=d;s.paid+=d;s.put+=d;if(users[s.id].chips<=0)s.allin=true}

function start(t,azi){
  clearTimeout(t.timer);
  let ins;
  if(azi)ins=t.seats.filter(s=>s.in);
  else{
    ins=t.seats.filter(s=>users[s.id].chips>=t.ante);
    if(ins.length<2){t.log='Нужно минимум 2 игрока с фишками';return}
    t.carry=0;
  }
  t.seats.forEach(s=>{s.in=ins.includes(s);s.hand=[];s.put=0;s.paid=0;s.folded=false;s.looked=false;s.allin=false;s.wins=0});
  const wi=ins.findIndex(s=>s.id===t.winner);
  t.order=azi?ins:[...ins.slice(wi+1),...ins.slice(0,wi+1)]; // торги начинает игрок слева от победителя
  if(!azi)ins.forEach(s=>{s.paid=t.ante;users[s.id].chips-=t.ante});
  const d=[];for(let s=0;s<3;s++)for(let r=0;r<9;r++)d.push({s,r}); // 27 карт, без крестей
  for(let i=d.length-1;i>0;i--){const j=Math.random()*(i+1)|0;[d[i],d[j]]=[d[j],d[i]]}
  ins.forEach(s=>s.hand=d.splice(0,3));
  t.trump=d[0];t.board=[];t.lastTrick=null;t.high=0;t.lead=t.order[0].id;t.acted=new Set();t.turn=0;
  t.phase='bid';t.log=azi?'АЗИ: новые торги':'Торги';save();
}
function bid(t,s,m){
  const q=users[s.id];
  if(m.a==='look'){s.looked=true;return}
  if(m.a==='fold')s.folded=true;
  else if(m.a==='call')pay(t,s,t.high-s.put);
  else if(m.a==='raise'||m.a==='blind'){
    let n=Math.floor(+m.n);if(!(n>0))return;
    if(m.a==='blind'){if(s.looked)return;n*=2}else if(!s.looked)return; // вслепую считается x2
    n=Math.min(n,q.chips);
    if(s.put+n<=t.high&&n<q.chips)return;
    pay(t,s,n);
    if(s.put>t.high){t.high=s.put;t.lead=s.id;t.acted=new Set()}
  }else return;
  t.acted.add(s.id);adv(t);
}
function adv(t){
  const r=act(t);
  if(r.length===1)return finish(t,r[0]);
  if(r.every(s=>s.allin||(t.acted.has(s.id)&&s.put===t.high)))return play0(t);
  let i=t.turn;do{i=(i+1)%t.order.length}while(t.order[i].folded||t.order[i].allin);
  t.turn=i;
}
function play0(t){
  t.phase='play';t.order.forEach(s=>s.looked=true);
  const L=t.order.find(s=>s.id===t.lead&&!s.folded)||t.order.find(s=>!s.folded);
  t.turn=t.order.indexOf(L);t.log='Ходит '+L.name;
}
function legal(t,s,i){
  const c=s.hand[i];if(!c)return false;
  if(!t.board.length)return true;
  const ls=t.board[0].c.s;
  if(s.hand.some(x=>x.s===ls))return c.s===ls;
  if(s.hand.some(x=>x.s===t.trump.s))return c.s===t.trump.s;
  return true;
}
function play(t,s,i){
  if(!legal(t,s,i))return;
  const c=s.hand.splice(i,1)[0];t.board.push({id:s.id,c});
  if(t.board.length<act(t).length){
    let k=t.turn;do{k=(k+1)%t.order.length}while(t.order[k].folded);t.turn=k;return;
  }
  const ls=t.board[0].c.s,tr=t.trump;
  const pw=c=>c.s===tr.s?20+(tr.r===8&&c.r===0?100:c.r):c.s===ls?c.r:-1; // «Шоха»: туз-козырь => козырная шестёрка старшая
  const best=t.board.reduce((a,b)=>pw(b.c)>pw(a.c)?b:a);
  const w=t.order.find(x=>x.id===best.id);w.wins++;
  t.lastTrick={board:t.board,w:w.id};t.board=[];
  if(w.wins>=2)return finish(t,w);
  if(!w.hand.length)return azi(t);
  t.turn=t.order.indexOf(w);t.log='Ходит '+w.name;
}
function finish(t,w){
  const W=w.paid;let get=t.carry;
  t.seats.forEach(s=>{if(!s.in)return;const m=Math.min(s.paid,W);get+=m;if(s!==w)users[s.id].chips+=s.paid-m}); // пропорция при нехватке фишек
  users[w.id].chips+=get;t.winner=w.id;t.carry=0;t.phase='idle';t.log=w.name+' забрал банк: '+get;save();
}
function azi(t){
  let p=pot(t);const c=Math.min(500,p);
  if(ADMIN)users[ADMIN].chips+=c;p-=c;t.carry=p;
  const con=t.order.filter(s=>!s.folded&&s.wins===1);
  t.con=con.map(s=>s.id);t.offer={};t.dec={};
  t.seats.forEach(s=>{if(s.in&&!t.con.includes(s.id))t.offer[s.id]=s.folded?p:Math.ceil(p/2)});
  t.phase='azi';t.log='АЗИ! Банк '+p+' (комиссия стола '+c+')';save();
  if(!Object.keys(t.offer).length)aziGo(t);
}
function aziGo(t){
  const j=Object.keys(t.offer).filter(id=>t.dec[id]);
  j.forEach(id=>{users[id].chips-=t.offer[id];t.carry+=t.offer[id]});
  t.seats.forEach(s=>s.in=t.con.includes(s.id)||j.includes(s.id));
  t.winner=null;start(t,true);
}
function arm(t){
  clearTimeout(t.timer);if(t.phase==='idle')return;
  t.timer=setTimeout(()=>{
    if(t.phase==='azi'){for(const id in t.offer)if(!(id in t.dec))t.dec[id]=false;aziGo(t)}
    else{
      const s=t.order[t.turn];
      if(t.phase==='bid')bid(t,s,{a:s.put===t.high?'call':'fold'});
      else play(t,s,s.hand.findIndex((_,k)=>legal(t,s,k)));
    }
    arm(t);sync();
  },45000);
}
function view(t,u){
  const s=t.seats.find(x=>x.id===u),cur=(t.phase==='bid'||t.phase==='play')&&t.order[t.turn];
  return{id:t.id,ante:t.ante,phase:t.phase,pot:pot(t),high:t.high,trump:t.phase!=='idle'?t.trump:null,
    turn:cur&&cur.id,board:t.board,last:t.lastTrick,log:t.log,me:u,inv:BOT,
    offer:t.phase==='azi'&&t.offer[u]!=null&&!(u in t.dec)?t.offer[u]:null,
    seats:t.seats.map(x=>({id:x.id,name:x.name,chips:users[x.id].chips,in:x.in,folded:x.folded,put:x.put,wins:x.wins,n:x.hand?x.hand.length:0})),
    hand:s&&t.phase!=='idle'&&t.phase!=='azi'&&(s.looked||t.phase==='play')?s.hand:null,
    looked:!!(s&&s.looked),mine:!!s&&cur===s,seated:!!s};
}
function sync(){
  for(const ws of conns){
    if(!ws.u||ws.readyState!==1)continue;
    ws.send(JSON.stringify(ws.t?{v:'t',t:view(ws.t,ws.u),chips:users[ws.u].chips,err:ws.err}:{v:'l',chips:users[ws.u].chips,err:ws.err,
      tables:Object.values(tables).map(t=>({id:t.id,ante:t.ante,n:t.seats.length})),admin:ws.u===ADMIN,
      users:ws.u===ADMIN?Object.entries(users).map(([id,u])=>({id,name:u.name,chips:u.chips})):undefined}));
    ws.err='';
  }
}
function join(ws,t){
  if(!t.seats.find(s=>s.id===ws.u)){
    if(t.phase!=='idle'||t.seats.length>=8){ws.err='Нельзя сесть: идёт игра или стол полон';return}
    t.seats.push({id:ws.u,name:users[ws.u].name,hand:[]});
  }
  ws.t=t;
}
const srv=http.createServer((q,r)=>{r.setHeader('content-type','text/html;charset=utf-8');r.end(fs.readFileSync(__dirname+'/index.html'))});
const wss=new WebSocketServer({server:srv});
wss.on('connection',ws=>{
  conns.add(ws);ws.on('close',()=>conns.delete(ws));
  ws.on('message',raw=>{
    let m;try{m=JSON.parse(raw)}catch{return}
    if(m.a==='auth'){
      const u=auth(m.init)||(DEV&&m.dev?{id:'dev_'+m.dev,name:m.dev}:null);
      if(!u)return ws.send('{"v":"x"}');
      ws.u=u.id;users[u.id]=users[u.id]||{name:u.name,chips:0};users[u.id].name=u.name;save();
      for(const t of Object.values(tables))if(t.seats.find(s=>s.id===u.id))ws.t=t;
      if(m.join&&tables[m.join])join(ws,tables[m.join]);
      return sync();
    }
    if(!ws.u)return;
    const t=ws.t,s=t&&t.seats.find(x=>x.id===ws.u),mine=s&&t.order&&t.order[t.turn]===s;
    if(m.a==='create'){const id=String(tid++);tables[id]={id,ante:Math.max(1,Math.floor(+m.n)||100),seats:[],phase:'idle',carry:0};join(ws,tables[id])}
    else if(m.a==='join'&&tables[m.id])join(ws,tables[m.id]);
    else if(m.a==='leave'&&t&&t.phase==='idle'){t.seats=t.seats.filter(x=>x.id!==ws.u);ws.t=null;if(!t.seats.length)delete tables[t.id]}
    else if(m.a==='back')ws.t=null;
    else if(m.a==='start'&&s&&t.phase==='idle')start(t);
    else if(m.a==='give'&&ws.u===ADMIN&&users[m.to]){users[m.to].chips=Math.max(0,users[m.to].chips+Math.floor(+m.n||0));save()}
    else if(t&&t.phase==='bid'&&mine)bid(t,s,m);
    else if(t&&t.phase==='play'&&mine&&m.a==='play')play(t,s,m.i);
    else if(t&&t.phase==='azi'&&m.a==='azi'&&t.offer[ws.u]!=null&&!(ws.u in t.dec)){
      t.dec[ws.u]=!!m.yes&&users[ws.u].chips>=t.offer[ws.u];
      if(Object.keys(t.offer).every(id=>id in t.dec))aziGo(t);
    }
    if(t)arm(t);sync();
  });
});
srv.listen(E.PORT||3000,()=>console.log('AZI on',E.PORT||3000));
if(TOKEN)(async function poll(o=0){
  try{
    const r=await(await fetch(`https://api.telegram.org/bot${TOKEN}/getUpdates?timeout=30&offset=${o}`)).json();
    for(const u of r.result||[]){o=u.update_id+1;const m=u.message;
      if(m&&m.text&&m.text.startsWith('/start'))fetch(`https://api.telegram.org/bot${TOKEN}/sendMessage`,{method:'POST',headers:{'content-type':'application/json'},
        body:JSON.stringify({chat_id:m.chat.id,text:'АЗИ — играть с друзьями',reply_markup:{inline_keyboard:[[{text:'Играть',web_app:{url:APP}}]]}})});}
  }catch{await new Promise(r=>setTimeout(r,3000))}
  poll(o);
})();

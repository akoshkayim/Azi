const http=require('http'),fs=require('fs'),crypto=require('crypto');
const {WebSocketServer}=require('ws');
const E=process.env,TOKEN=E.BOT_TOKEN||'',ADMIN=String(E.ADMIN_ID||''),DEV=E.DEV==='1',APP=E.APP_URL||'',BOT=E.BOT_USER||'';
let users={};try{users=JSON.parse(fs.readFileSync('db.json'))}catch{}
if(ADMIN&&!users[ADMIN])users[ADMIN]={name:'Админ',chips:0};
let meta={azi:0};try{meta=JSON.parse(fs.readFileSync('meta.json'))}catch{}
const save=()=>{fs.writeFileSync('db.json',JSON.stringify(users));fs.writeFileSync('meta.json',JSON.stringify(meta))};
function giveChips(id,n,set){const u=users[id],old=u.chips;u.chips=Math.max(0,(set?0:u.chips)+Math.floor(+n||0));u.issued=(u.issued||0)+(u.chips-old)}
const TRICK_MS=4000; // сколько карты взятки лежат на столе
const AZI_KEEP=4000,AZI_JOIN=2000,WHITE_ANTE=500; // правила: остаток на кону при дележе АЗИ, вход в АЗИ, кон белого
let ICE=[{urls:'stun:stun.l.google.com:19302'}];try{if(E.ICE)ICE=JSON.parse(E.ICE)}catch{}
const tables={};let tid=1;const conns=new Set();
const dealerOf=t=>t.seats.find(x=>x.id===t.winner)||t.seats[0];
const act=t=>t.seats.filter(s=>s.in&&!s.folded);
const pot=t=>(t.phase==='azi'||t.phase==='azivote')?t.carry:t.carry+t.seats.reduce((a,s)=>a+(s.in?s.paid:0),0);

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
  let ins,wh=[];
  if(azi)ins=t.seats.filter(s=>s.in);
  else{
    const reg=t.seats.filter(s=>users[s.id].chips>=t.ante);
    wh=t.seats.filter(s=>users[s.id].chips<t.ante&&!users[s.id].whiteUsed);
    if(!reg.length||reg.length+wh.length<2){t.log='Нужно минимум 2 игрока с фишками';return}
    ins=t.seats.filter(s=>reg.includes(s)||wh.includes(s));
    t.carry=0;
  }
  t.seats.forEach(s=>{s.in=ins.includes(s);s.hand=[];s.put=0;s.paid=0;s.folded=false;s.looked=false;s.allin=false;s.wins=0;s.blinded=false;s.white=azi?(!!s.white&&s.in):wh.includes(s)});
  const did=azi?t.aziDealer:(t.seats.find(x=>x.id===t.winner)?t.winner:t.seats[0].id); // сдающий
  const wi=ins.findIndex(s=>s.id===did);
  t.dealerId=did;
  t.order=wi<0?ins:[...ins.slice(wi+1),...ins.slice(0,wi+1)]; // первым ходит слева от сдающего, сдающий последний
  const ante=wh.length?WHITE_ANTE:t.ante; // если есть белый, кон по 500
  if(!azi)ins.forEach(s=>{if(s.white){users[s.id].whiteUsed=true;return}const d=Math.min(ante,users[s.id].chips);users[s.id].chips-=d;s.paid=d});
  ins.forEach(s=>{if(s.white||users[s.id].chips<=0)s.allin=true});
  const d=[];for(let s=0;s<3;s++)for(let r=0;r<9;r++)d.push({s,r}); // 27 карт, без крестей
  for(let i=d.length-1;i>0;i--){const j=Math.random()*(i+1)|0;[d[i],d[j]]=[d[j],d[i]]}
  ins.forEach(s=>s.hand=d.splice(0,3));
  t.trump=d[0];t.board=[];t.lastTrick=null;t.resolving=null;t.high=0;t.lastRaise=null;t.asked=[];t.option=false;t.optDone=false;t.blindOpen=true;t.lead=t.order[0].id;t.acted=new Set();t.turn=0;
  t.phase='bid';t.log=azi?'АЗИ: новые торги':(wh.length?'Белый: '+wh.map(s=>s.name).join(', ')+'. Кон по '+WHITE_ANTE:'Торги');
  const f=t.order.findIndex(s=>!s.allin);if(f<0)play0(t);else t.turn=f;
  save();
}
function closeBlind(t){t.blindOpen=false;t.order.forEach(x=>{if(!x.folded)x.looked=true})}
function bid(t,s,m){
  const q=users[s.id],OPEN='Сначала откройте карты (Ашу)';
  if(m.a==='done'){if(!t.option||t.lead!==s.id)return;t.option=false;t.optDone=true;adv(t);return}
  if(t.option&&m.a!=='raise')return 'Все уравняли: можно повысить (Ары) или начать игру';
  if(m.a==='look'){s.looked=true;return}
  if(m.a==='fold'){if(!s.looked)return OPEN;s.folded=true}
  else if(m.a==='call'){
    if(!s.looked)return OPEN;
    if(!(t.high>0))return 'Ставки ещё нет: выберите Ары или Пас';
    closeBlind(t);pay(t,s,t.high-s.put);
  }else if(m.a==='raise'||m.a==='blind'){
    let n=Math.floor(+m.n);if(!(n>0))return 'Введите сумму';
    if(m.a==='blind'){
      if(!t.blindOpen)return 'Ход недоступен: кто-то уже уравнял или повысил';
      if(s.id===t.dealerId)return 'Сдающий не может давать ход. Нажмите Ашу';
      if(s.looked||s.blinded)return;
      n*=2; // ход вслепую считается x2
    }else if(!s.looked)return OPEN;
    n=Math.min(n,q.chips);
    if(s.put+n<=t.high&&n<q.chips)return 'Ставка должна быть больше текущей ('+t.high+'). У вас выйдет '+(s.put+n);
    const L={id:s.id,prevHigh:t.high,prevActed:[...t.acted]};
    if(m.a==='blind'){s.blinded=true;s.looked=true}else closeBlind(t);
    pay(t,s,n);
    if(s.put>t.high){t.lastRaise=m.a==='raise'?L:null;t.asked=[]; // «Без» можно просить только после повышения (Ары), не после Хода
    t.option=false;t.high=s.put;t.lead=s.id;t.acted=new Set()}
  }else return;
  t.acted.add(s.id);adv(t);
}
function without(t,s){ // «Без»: игрок отменяет свою последнюю прибавку, уравнивает прежнюю ставку и ходит первым
  const L=t.lastRaise;if(!L||L.id!==s.id)return 'Нечего отменять';
  if(!(t.asked&&t.asked.length))return 'Никто не просит «Без»';
  t.seats.forEach(x=>{if(x.in&&x.put>L.prevHigh){const d=x.put-L.prevHigh;users[x.id].chips+=d;x.paid-=d;x.put=L.prevHigh;if(!x.white&&users[x.id].chips>0)x.allin=false}});
  t.high=L.prevHigh;t.lead=s.id;t.acted=new Set([...L.prevActed,s.id]);t.lastRaise=null;t.asked=[];t.optDone=true;t.option=false;
  adv(t,true);
}
function adv(t,stay){
  const r=act(t);
  if(r.length===1)return finish(t,r[0]);
  const needs=s=>!s.allin&&!(t.acted.has(s.id)&&s.put===t.high);
  if(!r.some(needs)){
    const L=r.find(s=>s.id===t.lead); // все уравняли: тот, кто дал ход, может ещё повысить (Ары)
    if(L&&!L.allin&&!L.white&&!t.optDone&&t.high>0){t.option=true;t.optDone=true; /* право повысить даётся один раз за кон */t.turn=t.order.indexOf(L);t.log=L.name+': все уравняли. Ары или играть';return}
    t.option=false;return play0(t);
  }
  const cur=t.order[t.turn];
  if(stay&&!cur.folded&&needs(cur))return;
  let i=t.turn;do{i=(i+1)%t.order.length}while(t.order[i].folded||!needs(t.order[i]));
  t.turn=i;
}
function play0(t){
  t.phase='play';t.lastRaise=null;t.asked=[];t.option=false;t.order.forEach(s=>s.looked=true);
  const nf=t.order.filter(s=>!s.folded);
  const L=nf.find(s=>s.id===t.lead)||nf.slice().sort((a,b)=>b.put-a.put)[0];
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
  if(t.resolving||!legal(t,s,i))return;
  const c=s.hand.splice(i,1)[0];t.board.push({id:s.id,c});
  if(t.board.length<act(t).length){
    let k=t.turn;do{k=(k+1)%t.order.length}while(t.order[k].folded);t.turn=k;return;
  }
  const ls=t.board[0].c.s,tr=t.trump;
  const pw=c=>c.s===tr.s?20+(tr.r===8&&c.r===0?100:c.r):c.s===ls?c.r:-1; // «Шоха»: туз-козырь => козырная шестёрка старшая
  const best=t.board.reduce((a,b)=>pw(b.c)>pw(a.c)?b:a);
  const w=t.order.find(x=>x.id===best.id);w.wins++;
  t.lastTrick={board:t.board,w:w.id};
  t.resolving=w.id;t.turn=t.order.indexOf(w);t.log=w.name+' берёт взятку';
  setTimeout(()=>{ // карты остаются на столе 2.5 секунды
    if(t.resolving!==w.id)return;
    t.resolving=null;t.board=[];
    if(w.wins>=2)finish(t,w);
    else if(!w.hand.length)azi(t,w.id);
    else{t.turn=t.order.indexOf(w);t.log='Ходит '+w.name}
    arm(t);sync();
  },TRICK_MS);
}
function finish(t,w){
  const W=w.white?Infinity:w.paid;/* белый забирает весь банк */let get=t.carry;
  t.seats.forEach(s=>{if(!s.in)return;const m=Math.min(s.paid,W);get+=m;if(s!==w)users[s.id].chips+=s.paid-m}); // пропорция при нехватке фишек
  users[w.id].chips+=get;t.winner=w.id;t.carry=0;t.phase='idle';t.log=w.name+' забрал банк: '+get;save();
}
function azi(t,wid){
  let p=pot(t);const c=Math.min(500,p);
  meta.azi=(meta.azi||0)+c;p-=c;t.carry=p; // комиссия копится в «АЗИ» кассы
  t.con=t.order.filter(s=>!s.folded&&s.wins===1).map(s=>s.id);
  t.aziDealer=wid;t.vote={};t.phase='azivote';
  t.log='АЗИ! Банк '+p+' (комиссия '+c+'). Игроки АЗИ решают: разделить или оставить на кону';
}
function aziVote(t){
  const split=t.con.every(id=>t.vote[id]===true);
  if(split){
    const k=t.con.length,keep=Math.min(AZI_KEEP,t.carry),each=Math.floor((t.carry-keep)/k);
    t.con.forEach(id=>users[id].chips+=each);t.carry-=each*k;
    t.log='АЗИ разделили: по '+each+' каждому, на кону '+t.carry;
  }else t.log='АЗИ: вся сумма остаётся на кону: '+t.carry;
  const p=t.carry;t.offer={};t.dec={};
  t.seats.forEach(s=>{if(s.in&&!t.con.includes(s.id))t.offer[s.id]=split?AZI_JOIN:Math.ceil(p/2)});
  t.phase='azi';
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
    if(t.phase==='azivote'){t.con.forEach(id=>{if(!(id in t.vote))t.vote[id]=false});aziVote(t)}
    else if(t.phase==='azi'){for(const id in t.offer)if(!(id in t.dec))t.dec[id]=false;aziGo(t)}
    else{
      const s=t.order[t.turn];
      if(t.phase==='bid'){s.looked=true;bid(t,s,{a:t.option?'done':((s.put===t.high&&t.high>0)?'call':'fold')})}
      else play(t,s,s.hand.findIndex((_,k)=>legal(t,s,k)));
    }
    arm(t);sync();
  },45000);
}
function view(t,u){
  const s=t.seats.find(x=>x.id===u),cur=(t.phase==='bid'||t.phase==='play')&&!t.resolving&&t.order[t.turn];
  return{id:t.id,ante:t.ante,phase:t.phase,pot:t.phase==='idle'?0:pot(t),high:t.phase==='idle'?0:t.high,trump:t.phase!=='idle'?t.trump:null,
    turn:cur&&cur.id,board:t.board,win:t.resolving||null,last:t.lastTrick,log:t.log,me:u,inv:BOT,
    offer:t.phase==='azi'&&t.offer[u]!=null&&!(u in t.dec)?t.offer[u]:null,
    seats:t.seats.map(x=>({id:x.id,name:x.name,chips:users[x.id].chips,in:x.in,folded:t.phase!=='idle'&&x.folded,put:t.phase==='idle'?0:x.put,white:!!x.white,voice:!!(t.voice&&t.voice.has(x.id)),dealer:t.phase!=='idle'&&x.id===t.dealerId,wins:t.phase==='idle'?0:x.wins,n:x.hand?x.hand.length:0})),
    hand:s&&t.phase!=='idle'&&t.phase!=='azi'&&(s.looked||t.phase==='play')?s.hand:null,
    looked:!!(s&&s.looked),option:t.phase==='bid'&&!!t.option,watchers:[...conns].filter(o=>o.t===t&&o.u&&!t.seats.some(x=>x.id===o.u)).length,canBlind:!!s&&t.phase==='bid'&&!!t.blindOpen&&!s.looked&&!s.blinded&&s.id!==t.dealerId,canWithout:!!s&&t.phase==='bid'&&!!t.lastRaise&&t.lastRaise.id===u&&!!(t.asked&&t.asked.length),canAsk:!!s&&t.phase==='bid'&&!!t.lastRaise&&t.lastRaise.id!==u&&s.in&&!s.folded&&!s.white&&!(t.asked||[]).includes(u),asked:(t.asked||[]).map(id=>(t.seats.find(x=>x.id===id)||{}).name),canVote:t.phase==='azivote'&&!!t.con&&t.con.includes(u)&&!(u in t.vote),isDealer:t.dealerId===u,azi:{keep:AZI_KEEP,join:AZI_JOIN},blinded:!!(s&&s.blinded),canDeal:!!s&&dealerOf(t)===s,dealer:(dealerOf(t)||{}).name,mine:!!s&&cur===s,seated:!!s};
}
function sync(){
  for(const ws of conns){
    if(!ws.u||ws.readyState!==1)continue;
    ws.send(JSON.stringify(ws.t?{v:'t',ice:ICE,t:view(ws.t,ws.u),chips:users[ws.u].chips,err:ws.err}:{v:'l',chips:users[ws.u].chips,err:ws.err,
      tables:Object.values(tables).map(t=>({id:t.id,ante:t.ante,n:t.seats.length})),admin:ws.u===ADMIN,azi:ws.u===ADMIN?(meta.azi||0):undefined,
      users:ws.u===ADMIN?Object.entries(users).map(([id,u])=>({id,name:u.name,chips:u.chips,issued:u.issued||0})):undefined}));
    ws.err='';
  }
}
function vsend(t,except,msg){for(const o of conns)if(o.u&&o.t===t&&o.u!==except&&o.readyState===1)o.send(JSON.stringify(msg))}
function vleave(ws){const t=ws.t;if(!t||!t.voice||t.voice.get(ws.u)!==ws)return;t.voice.delete(ws.u);vsend(t,ws.u,{v:'sig',type:'left',id:ws.u})}
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
  conns.add(ws);ws.on('error',()=>{});ws.on('close',()=>{conns.delete(ws);vleave(ws);sync()});
  ws.on('message',raw=>{try{handle(raw)}catch(e){console.error(e)}});
  function handle(raw){
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
    if(m.a==='ping'){ws.send('{"v":"p"}');return} // пинг не должен сбрасывать таймер хода
    if(m.a==='sig'){const o=t&&t.voice&&t.voice.get(ws.u)===ws&&t.voice.get(m.to);if(o&&o.readyState===1)o.send(JSON.stringify({v:'sig',type:'data',from:ws.u,data:m.data}));return}
    if(m.a==='vjoin'&&t&&s){t.voice=t.voice||new Map();const peers=[...t.voice.keys()].filter(id=>id!==ws.u);t.voice.set(ws.u,ws);ws.send(JSON.stringify({v:'sig',type:'peers',peers}));sync();return}
    if(m.a==='vleave'){vleave(ws);sync();return}
    if(m.a==='create'){const id=String(tid++);tables[id]={id,ante:Math.max(1,Math.floor(+m.n)||100),seats:[],phase:'idle',carry:0,board:[],high:0,order:[],turn:0};join(ws,tables[id])}
    else if(m.a==='watch'&&tables[m.id])ws.t=tables[m.id];
    else if(m.a==='join'&&tables[m.id])join(ws,tables[m.id]);
    else if(m.a==='leave'&&t&&t.phase==='idle'){vleave(ws);t.seats=t.seats.filter(x=>x.id!==ws.u);ws.t=null;if(!t.seats.length)delete tables[t.id]}
    else if(m.a==='back'){vleave(ws);ws.t=null}
    else if(m.a==='start'&&s&&t.phase==='idle'&&dealerOf(t)===s)start(t);
    else if(m.a==='ask'&&t&&s&&t.phase==='bid'&&t.lastRaise&&t.lastRaise.id!==ws.u&&s.in&&!s.folded&&!s.white&&!(t.asked||[]).includes(ws.u))t.asked=[...(t.asked||[]),ws.u];
    else if(m.a==='without'&&t&&s&&t.phase==='bid'){const e=without(t,s);if(e)ws.err=e}
    else if(t&&t.phase==='azivote'&&m.a==='vote'&&t.con.includes(ws.u)&&!(ws.u in t.vote)){t.vote[ws.u]=!!m.split;if(t.con.every(id=>id in t.vote))aziVote(t)}
    else if(m.a==='give'&&ws.u===ADMIN&&users[m.to]){giveChips(m.to,m.n,m.set);save()}
    else if(t&&t.phase==='bid'&&mine){const e=bid(t,s,m);if(e)ws.err=e}
    else if(t&&t.phase==='play'&&mine&&m.a==='play')play(t,s,m.i);
    else if(t&&t.phase==='azi'&&m.a==='azi'&&t.offer[ws.u]!=null&&!(ws.u in t.dec)){
      t.dec[ws.u]=!!m.yes&&users[ws.u].chips>=t.offer[ws.u];
      if(Object.keys(t.offer).every(id=>id in t.dec))aziGo(t);
    }
    if(t)arm(t);sync();
  }
});
process.on('uncaughtException',e=>console.error(e));
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

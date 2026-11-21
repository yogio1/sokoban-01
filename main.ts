// Push-optimal Sokoban solver for make.fun sokoban-solver-01 (generator: hallway row + rooms above/below).
// Rooms are detected structurally (halves of the board split by the player's hallway row), solved independently
// with push-optimal A* (boxes+player-region state, pull-distance matching heuristic), then stitched.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIRS: [number, number, string][] = [[0,-1,'u'],[0,1,'d'],[-1,0,'l'],[1,0,'r']];
function parse(text:string){
  const rows=text.split('\n').filter(r=>r.length>0);
  const w=Math.max(...rows.map(r=>r.length)); const h=rows.length;
  const wall=new Uint8Array(w*h), goal=new Uint8Array(w*h);
  const boxes:number[]=[]; let player=-1;
  rows.forEach((row,y)=>{ for(let x=0;x<w;x++){ const ch=row[x]??'#'; const i=y*w+x;
    wall[i]=ch==='#'?1:0; if('.*+'.includes(ch)) goal[i]=1; if('$*'.includes(ch)) boxes.push(i); if('@+'.includes(ch)) player=i; }});
  return {w,h,wall,goal,boxes,player};
}
function reach(w:number,h:number,wall:Uint8Array,boxes:Set<number>,start:number){
  const seen=new Uint8Array(w*h);
  if(start<0||wall[start]||boxes.has(start)) return seen;
  const st=[start]; seen[start]=1;
  while(st.length){ const c=st.pop()!; const cx=c%w, cy=(c/w)|0;
    for(const [dx,dy] of DIRS){ const nx=cx+dx, ny=cy+dy;
      if(nx<0||ny<0||nx>=w||ny>=h)continue; const n=ny*w+nx;
      if(!seen[n]&&!wall[n]&&!boxes.has(n)){seen[n]=1;st.push(n);} } }
  return seen;
}
function solveRoom(w: number, h: number, wall: Uint8Array, goal: Uint8Array, roomCells: number[],
                   boxes0: number[], player0: number, budget = 2_000_000): { pushes: { box: number; dir: number }[] } | null {
  const N = w * h;
  const room = new Set(roomCells);
  const roomGoals = roomCells.filter(c => goal[c]);
  if (roomGoals.length < boxes0.length) return null;
  // pull-distance from each room goal within room
  const hMin = new Int16Array(N).fill(-1);
  for (const g of roomGoals) {
    const d = new Int16Array(N).fill(-1); d[g] = 0; const q = [g];
    while (q.length) { const c = q.shift()!; const cx = c % w, cy = (c / w) | 0;
      for (const [dx, dy] of DIRS) { const nx = cx + dx, ny = cy + dy, px = cx + 2 * dx, py = cy + 2 * dy;
        if (px < 0 || py < 0 || px >= w || py >= h) continue;
        const n = ny * w + nx, p = py * w + px;
        if (!room.has(n) || !room.has(p) || wall[n] || wall[p]) continue;
        if (d[n] === -1) { d[n] = d[c] + 1; q.push(n); } } }
    for (const p of roomCells) if (d[p] >= 0 && (hMin[p] === -1 || d[p] < hMin[p])) hMin[p] = d[p];
  }
  // better heuristic: greedy matching of boxes to goals on pull-distance (admissible when each box min matched)
  const hOf = (boxes: number[]) => {
    // per-box sorted distances to goals; box i can be matched to any goal: use greedy assignment
    const used = new Set<number>(); let s = 0;
    const pairs: { b: number; g: number; d: number }[] = [];
    for (const b of boxes) for (const g of roomGoals) {
      // distance from b to g along pulls — approximate by hMin (min over goals) is weaker; compute per-goal dist lazily:
      void g;
    }
    for (const b of boxes) { if (hMin[b] < 0) return -1; s += hMin[b]; }
    return s;
  };
  const reachRoom = (boxes: Set<number>, start: number) => {
    const seen = new Uint8Array(N);
    if (start < 0 || wall[start] || boxes.has(start)) return seen;
    const st = [start]; seen[start] = 1;
    while (st.length) { const c = st.pop()!; const cx = c % w, cy = (c / w) | 0;
      for (const [dx, dy] of DIRS) { const nx = cx + dx, ny = cy + dy;
        if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue;
        const n = ny * w + nx;
        if (!seen[n] && room.has(n) && !wall[n] && !boxes.has(n)) { seen[n] = 1; st.push(n); } } }
    return seen;
  };
  const regionMin = (boxes: number[], seed: number) => {
    const s = reachRoom(new Set(boxes), seed); let m = -1;
    for (const c of roomCells) if (s[c]) { m = c; break; }
    return m;
  };
  const startRegion = regionMin(boxes0, player0);
  if (startRegion < 0) return null;
  type Node = { g: number; f: number; boxes: number[]; region: number; parent: Node | null; box: number; dir: number };
  const open: Node[] = [];
  const h0 = hOf(boxes0);
  if (h0 < 0) return null;
  open.push({ g: 0, f: h0, boxes: boxes0, region: startRegion, parent: null, box: 0, dir: 0 });
  const best = new Map<string, number>();
  let exp = 0, end: Node | null = null;
  while (open.length) {
    let bi = 0; for (let i = 1; i < open.length; i++) if (open[i].f < open[bi].f) bi = i;
    const cur = open.splice(bi, 1)[0];
    exp++; if (exp > budget) return null;
    if (cur.boxes.every(b => goal[b])) { end = cur; break; }
    const seen = reachRoom(new Set(cur.boxes), cur.region);
    const boxSet = new Set(cur.boxes);
    for (const b of cur.boxes) {
      const bx = b % w, by = (b / w) | 0;
      for (let d = 0; d < 4; d++) {
        const [dx, dy] = DIRS[d];
        const back = (by - dy) * w + (bx - dx), fwd = (by + dy) * w + (bx + dx);
        if (back < 0 || back >= N || fwd < 0 || fwd >= N) continue;
        if (wall[fwd] || boxSet.has(fwd) || !room.has(fwd)) continue;
        if (!seen[back]) continue;
        const nb = cur.boxes.map(x => x === b ? fwd : x).sort((a, z) => a - z);
        if (!goal[fwd]) {
          const x = fwd % w, y = (fwd / w) | 0;
          const W = (i: number) => i < 0 || wall[i] || !room.has(i);
          const up = W(fwd - w), dn = W(fwd + w), lf = W(fwd - 1), rt = W(fwd + 1);
          if ((up && lf) || (up && rt) || (dn && lf) || (dn && rt)) continue;
        }
        const hh = hOf(nb); if (hh < 0) continue;
        const reg = regionMin(nb, b); if (reg < 0) continue;
        const key = nb.join(',') + '|' + reg;
        const g2 = cur.g + 1;
        const prev = best.get(key); if (prev !== undefined && prev <= g2) continue;
        best.set(key, g2);
        open.push({ g: g2, f: g2 + hh, boxes: nb, region: reg, parent: cur, box: b, dir: d });
      }
    }
  }
  if (!end) return null;
  const pushes: { box: number; dir: number }[] = [];
  for (let x: Node | null = end; x && x.parent; x = x.parent) pushes.unshift({ box: x.box, dir: x.dir });
  return { pushes };
}

function solveLevel(text: string): string {
  const { w, h, wall, goal, boxes, player } = parse(text);
  const N = w * h;
  const yHall = Math.floor(player / w);
  // rooms: components within each half (boxes as floor), with >=1 adjacent box
  const roomDefs: { cells: number[]; boxes: number[]; door: number }[] = [];
  for (const half of [0, 1]) {
    const ylo = half === 0 ? 1 : yHall + 1, yhi = half === 0 ? yHall - 1 : h - 2;
    if (ylo > yhi) continue;
    const inHalf = (c: number) => { const y = Math.floor(c / w); return y >= ylo && y <= yhi; };
    const comp = new Int32Array(N).fill(-1);
    const comps: number[][] = [];
    for (let y = ylo; y <= yhi; y++) for (let x = 1; x < w - 1; x++) {
      const i = y * w + x;
      if (wall[i] || comp[i] >= 0) continue;
      const id = comps.length; const cells: number[] = [];
      const st = [i]; comp[i] = id;
      while (st.length) { const c = st.pop()!; cells.push(c); const cx = c % w, cy = Math.floor(c / w);
        for (const [dx, dy] of DIRS) { const nx = cx + dx, ny = cy + dy;
          if (nx < 1 || ny < ylo || nx >= w - 1 || ny > yhi) continue;
          const n = ny * w + nx;
          if (!wall[n] && comp[n] < 0) { comp[n] = id; st.push(n); } } }
      comps.push(cells);
    }
    for (const cells of comps) {
      const bs = [...new Set(cells.flatMap(c => DIRS.map(([dx, dy]) => (Math.floor(c / w) + dy) * w + (c % w) + dx)).filter(n => boxes.includes(n)))];
      if (bs.length === 0) continue;
      // door: room cell adjacent to a hallway-row floor cell
      let door = -1;
      for (const c of cells) {
        const cy = Math.floor(c / w);
        for (const [dx, dy] of DIRS) {
          const n = (cy + dy) * w + (c % w + dx);
          if (Math.floor(n / w) === yHall && !wall[n]) { door = c; break; }
        }
        if (door >= 0) break;
      }
      if (door < 0) continue;
      roomDefs.push({ cells, boxes: bs, door });
    }
  }
  // all boxes must be assigned
  const assigned = roomDefs.flatMap(r => r.boxes);
  if (assigned.length !== boxes.length) return '';
  const hallCellOf = (door: number) => {
    const cy = Math.floor(door / w);
    for (const [dx, dy] of DIRS) {
      const n = (cy + dy) * w + (door % w + dx);
      if (n >= 0 && n < N && Math.floor(n / w) === yHall && !wall[n]) return n;
    }
    return -1;
  };
  let curPlayer = player;
  const boxSet = new Set(boxes);
  let moves = '';
  const walk = (to: number) => {
    const p = walkPath(w, h, wall, boxSet, curPlayer, to);
    if (p === null) return false;
    moves += p; curPlayer = to; return true;
  };
  for (const room of roomDefs) {
    const hallSide = hallCellOf(room.door);
    if (hallSide < 0 || !walk(hallSide)) return '';
    // enter the room: if door cell is a box, push it inward first
    if (boxSet.has(room.door)) {
      const dx0 = (room.door % w) - (hallSide % w);
      const dy0 = Math.floor(room.door / w) - Math.floor(hallSide / w);
      const d = DIRS.findIndex(([dx, dy]) => dx === dx0 && dy === dy0);
      if (d < 0) return '';
      moves += DIRS[d][2].toUpperCase();
      boxSet.delete(room.door);
      const dest = (Math.floor(room.door / w) + DIRS[d][1]) * w + (room.door % w + DIRS[d][0]);
      boxSet.add(dest);
      curPlayer = room.door;
    } else {
      if (!walk(room.door)) return '';
    }
    const roomBoxes = room.boxes.filter(b => boxSet.has(b));
    const sol = solveRoom(w, h, wall, goal, room.cells, roomBoxes, room.door);
    if (sol === null) return '';
    for (const p of sol.pushes) {
      const [dx, dy] = DIRS[p.dir];
      const bx = p.box % w, by = Math.floor(p.box / w);
      const stand = (by - dy) * w + (bx - dx);
      if (!walk(stand)) return '';
      moves += DIRS[p.dir][2].toUpperCase();
      boxSet.delete(p.box);
      boxSet.add((by + dy) * w + (bx + dx));
      curPlayer = (by + dy) * w + (bx + dx);
    }
    // exit: walk back to door cell then hall
    if (!walk(room.door)) return '';
    moves += ''; // step out
    const dx0 = (hallSide % w) - (room.door % w);
    const dy0 = Math.floor(hallSide / w) - Math.floor(room.door / w);
    const m = DIRS.find(([dx, dy]) => dx === dx0 && dy === dy0);
    if (!m) return '';
    moves += m[2]; curPlayer = hallSide;
  }
  return moves;
  function walkPath(w2: number, h2: number, wall2: Uint8Array, boxes2: Set<number>, from: number, to: number): string | null {
    if (from === to) return '';
    const M = w2 * h2;
    const prev = new Int32Array(M).fill(-2); const prevD = new Int8Array(M);
    prev[from] = -1; const q = [from];
    while (q.length) { const c = q.shift()!; const cx = c % w2, cy = Math.floor(c / w2);
      for (let d = 0; d < 4; d++) { const [dx, dy] = DIRS[d];
        const nx = cx + dx, ny = cy + dy;
        if (nx < 0 || ny < 0 || nx >= w2 || ny >= h2) continue;
        const n = ny * w2 + nx;
        if (prev[n] !== -2 || wall2[n] || boxes2.has(n)) continue;
        prev[n] = c; prevD[n] = d;
        if (n === to) { let s = ''; let cu = n; while (cu !== from) { s += DIRS[prevD[cu]][2]; cu = prev[cu]; } return [...s].reverse().join(''); }
        q.push(n); } }
    return null;
  }
}


function walkPath(w2:number,h2:number,wall2:Uint8Array,boxes2:Set<number>,from:number,to:number):string|null{
  if(from===to) return '';
  const M=w2*h2; const prev=new Int32Array(M).fill(-2); const prevD=new Int8Array(M);
  prev[from]=-1; const q=[from];
  while(q.length){ const c=q.shift()!; const cx=c%w2, cy=Math.floor(c/w2);
    for(let d=0;d<4;d++){ const [dx,dy]=DIRS[d]; const nx=cx+dx, ny=cy+dy;
      if(nx<0||ny<0||nx>=w2||ny>=h2)continue; const n=ny*w2+nx;
      if(prev[n]!==-2||wall2[n]||boxes2.has(n))continue;
      prev[n]=c; prevD[n]=d;
      if(n===to){ let s=''; let cu=n; while(cu!==from){ s+=DIRS[prevD[cu]][2]; cu=prev[cu]; } return [...s].reverse().join(''); }
      q.push(n); } }
  return null;
}

function hallSideOf(w:number,h:number,wall:Uint8Array,gh:number,door:number){
  const cy=Math.floor(door/w);
  for(const [dx,dy] of DIRS){ const n=(cy+dy)*w+(door%w+dx); if(Math.floor(n/w)===gh&&!wall[n]) return n; }
  return -1;
}
function solveLevel2(text:string, verbose=false):string{
  const {w,h,wall,goal,boxes,player}=parse(text);
  const N=w*h; const gh=Math.floor(player/w);
  const rooms:{cells:number[],boxes:number[],door:number}[]=[];
  for(const half of [0,1]){
    const ylo=half===0?1:gh+1, yhi=half===0?gh-1:h-2;
    if(ylo>yhi) continue;
    const comp=new Int32Array(N).fill(-1); const comps:number[][]=[];
    for(let y=ylo;y<=yhi;y++)for(let x=1;x<w-1;x++){const i=y*w+x; if(wall[i]||comp[i]>=0)continue;
      const id=comps.length; const cells:number[]=[]; const st=[i]; comp[i]=id;
      while(st.length){const c=st.pop()!;cells.push(c);const cx=c%w,cy=Math.floor(c/w);
        for(const [dx,dy] of DIRS){const nx=cx+dx,ny=cy+dy; if(nx<1||ny<ylo||nx>=w-1||ny>yhi)continue; const n=ny*w+nx;
          if(!wall[n]&&comp[n]<0){comp[n]=id;st.push(n);}}}
      comps.push(cells);}
    for(const cells of comps){
      const bs=[...new Set(cells.flatMap(c=>DIRS.map(([dx,dy])=>(Math.floor(c/w)+dy)*w+(c%w)+dx)).filter(n=>boxes.includes(n)))];
      if(!bs.length) continue;
      let door=-1;
      for(const c of cells){const cy=Math.floor(c/w);
        for(const [dx,dy] of DIRS){const n=(cy+dy)*w+(c%w+dx); if(Math.floor(n/w)===gh&&!wall[n]){door=c;break;}}
        if(door>=0)break;}
      if(door<0) continue;
      rooms.push({cells, boxes:bs, door});
    }
  }
  const assigned=rooms.flatMap(r=>r.boxes);
  if(assigned.length!==boxes.length){ if(verbose) console.error('ASSIGN',assigned.length,boxes.length); return ''; }
  const boxSet=new Set(boxes);
  let cur=player, moves='';
  const walk=(to:number)=>{ const p=walkPath(w,h,wall,boxSet,cur,to); if(p===null) return false; moves+=p; cur=to; return true; };
  for(const room of rooms){
    const hs=hallSideOf(w,h,wall,gh,room.door);
    if(hs<0){ if(verbose) console.error('NOHALL'); return ''; }
    if(!walk(hs)){ if(verbose) console.error('WALK hall'); return ''; }
    // room cells extended by hall side cell so the search can push the door box inwards
    const cellsExt=[...room.cells, hs];
    const roomBoxes=room.boxes.filter(b=>boxSet.has(b));
    const sol=solveRoom(w,h,wall,goal,cellsExt,roomBoxes,hs);
    if(sol===null){ if(verbose) console.error('SOLVEROOM null boxes',roomBoxes.join(','),'entry',hs); return ''; }
    for(const p of sol.pushes){
      const [dx,dy]=DIRS[p.dir];
      const bx=p.box%w, by=Math.floor(p.box/w);
      const stand=(by-dy)*w+(bx-dx);
      if(!walk(stand)){ if(verbose) console.error('WALK stand',p.box,p.dir,stand,cur,[...boxSet].join(',')); return ''; }
      moves+=DIRS[p.dir][2].toUpperCase();
      boxSet.delete(p.box); const dest=(by+dy)*w+(bx+dx); boxSet.add(dest); cur=p.box;
    }
    if(!walk(room.door)){ if(verbose) console.error('WALK door'); return ''; }
    const dx0=(hs%w)-(room.door%w), dy0=Math.floor(hs/w)-Math.floor(room.door/w);
    const m=DIRS.findIndex(([dx,dy])=>dx===dx0&&dy===dy0);
    if(m<0){ if(verbose) console.error('NOEXIT'); return ''; }
    moves+=DIRS[m][2]; cur=hs;
  }
  return moves;
}

function gparse(text:string){
  const rows=text.split('\n').filter(r=>r.length>0);
  const w=Math.max(...rows.map(r=>r.length)); const h=rows.length;
  const wall=new Uint8Array(w*h), goal=new Uint8Array(w*h);
  const boxes:number[]=[]; let player=-1;
  rows.forEach((row,y)=>{ for(let x=0;x<w;x++){ const ch=row[x]??'#'; const i=y*w+x;
    wall[i]=ch==='#'?1:0; if('.*+'.includes(ch)) goal[i]=1; if('$*'.includes(ch)) boxes.push(i); if('@+'.includes(ch)) player=i; }});
  return {w,h,wall,goal,boxes,player};
}
function greach(w:number,h:number,wall:Uint8Array,boxes:Set<number>,start:number){
  const seen=new Uint8Array(w*h);
  if(start<0||wall[start]||boxes.has(start)) return seen;
  const st=[start]; seen[start]=1;
  while(st.length){ const c=st.pop()!; const cx=c%w, cy=(c/w)|0;
    for(const [dx,dy] of DIRS){ const nx=cx+dx, ny=cy+dy;
      if(nx<0||ny<0||nx>=w||ny>=h)continue; const n=ny*w+nx;
      if(!seen[n]&&!wall[n]&&!boxes.has(n)){seen[n]=1;st.push(n);} } }
  return seen;
}
function gsolve(text:string, budget=5_000_000):string{
  const {w,h,wall,goal,boxes,player}=gparse(text);
  const N=w*h;
  // pull-dist heuristic
  const goals:number[]=[]; for(let i=0;i<N;i++) if(goal[i]) goals.push(i);
  const hMin=new Int16Array(N).fill(-1);
  for(const g of goals){ const d=new Int16Array(N).fill(-1); d[g]=0; const q=[g];
    while(q.length){ const c=q.shift()!; const cx=c%w, cy=(c/w)|0;
      for(const [dx,dy] of DIRS){ const nx=cx+dx, ny=cy+dy, px=cx+2*dx, py=cy+2*dy;
        if(px<0||py<0||px>=w||py>=h)continue; const n=ny*w+nx, p=py*w+px;
        if(wall[n]||wall[p])continue; if(d[n]===-1){d[n]=d[c]+1;q.push(n);} } }
    for(let p=0;p<N;p++) if(d[p]>=0&&(hMin[p]===-1||d[p]<hMin[p])) hMin[p]=d[p];
  }
  const hOf=(bs:number[])=>{ let s=0; for(const b of bs){ if(hMin[b]<0) return -1; s+=hMin[b]; } return s; };
  const cornerDead=(p:number)=>{ if(goal[p]) return false;
    const x=p%w, y=(p/w)|0;
    const W=(i:number)=> i<0||wall[i];
    const up=W(p-w),dn=W(p+w),lf=W(p-1),rt=W(p+1);
    return (up&&lf)||(up&&rt)||(dn&&lf)||(dn&&rt);
  };
  const startBoxes=[...boxes].sort((a,b)=>a-b);
  const regionMin=(bs:number[],seed:number)=>{ const s=greach(w,h,wall,new Set(bs),seed); let m=-1;
    for(let i=0;i<N;i++) if(s[i]){m=i;break;} return m; };
  const startRegion=regionMin(startBoxes,player);
  type Node={g:number;f:number;boxes:number[];region:number;parent:Node|null;box:number;dir:number};
  const open:Node[]=[]; const h0=hOf(startBoxes);
  if(h0>=0&&startRegion>=0) open.push({g:0,f:h0,boxes:startBoxes,region:startRegion,parent:null,box:0,dir:0});
  const best=new Map<string,number>();
  let exp=0, end:Node|null=null;
  while(open.length){
    let bi=0; for(let i=1;i<open.length;i++) if(open[i].f<open[bi].f) bi=i;
    const cur=open.splice(bi,1)[0];
    exp++; if(exp>budget) return '';
    if(cur.boxes.every(b=>goal[b])){end=cur;break;}
    const seen=greach(w,h,wall,new Set(cur.boxes),cur.region);
    const boxSet=new Set(cur.boxes);
    for(const b of cur.boxes){ const bx=b%w, by=(b/w)|0;
      for(let d=0;d<4;d++){ const [dx,dy]=DIRS[d];
        const back=(by-dy)*w+(bx-dx), fwd=(by+dy)*w+(bx+dx);
        if(back<0||back>=N||fwd<0||fwd>=N)continue;
        if(wall[fwd]||boxSet.has(fwd))continue;
        if(!seen[back])continue;
        const nb=cur.boxes.map(x=>x===b?fwd:x).sort((a,z)=>a-z);
        if(cornerDead(fwd))continue;
        const hh=hOf(nb); if(hh<0)continue;
        const reg=regionMin(nb,b); if(reg<0)continue;
        const key=nb.join(',')+'|'+reg; const g2=cur.g+1;
        const prev=best.get(key); if(prev!==undefined&&prev<=g2)continue;
        best.set(key,g2);
        open.push({g:g2,f:g2+hh,boxes:nb,region:reg,parent:cur,box:b,dir:d});
      } }
  }
  if(!end) return '';
  const pushes:{box:number;dir:number}[]=[];
  for(let x:Node|null=end;x&&x.parent;x=x.parent) pushes.unshift({box:x.box,dir:x.dir});
  // rebuild with walks
  const boxSet=new Set(boxes);
  let ppos=player, moves='';
  for(const p of pushes){ const [dx,dy]=DIRS[p.dir];
    const bx=p.box%w, by=(p.box/w)|0;
    const stand=(by-dy)*w+(bx-dx);
    const walk=walkTo(w,h,wall,boxSet,ppos,stand); if(walk===null) return '';
    moves+=walk+DIRS[p.dir][2].toUpperCase();
    boxSet.delete(p.box); const dest=(by+dy)*w+(bx+dx); boxSet.add(dest); ppos=dest;
  }
  return moves;
  function walkTo(w2:number,h2:number,wall2:Uint8Array,boxes2:Set<number>,from:number,to:number):string|null{
    if(from===to) return '';
    const M=w2*h2; const prev=new Int32Array(M).fill(-2); const prevD=new Int8Array(M);
    prev[from]=-1; const q=[from];
    while(q.length){ const c=q.shift()!; const cx=c%w2, cy=(c/w2)|0;
      for(let d=0;d<4;d++){ const [dx,dy]=DIRS[d]; const nx=cx+dx, ny=cy+dy;
        if(nx<0||ny<0||nx>=w2||ny>=h2)continue; const n=ny*w2+nx;
        if(prev[n]!==-2||wall2[n]||boxes2.has(n))continue;
        prev[n]=c; prevD[n]=d;
        if(n===to){ let s=''; let cu=n; while(cu!==from){ s+=DIRS[prevD[cu]][2]; cu=prev[cu]; } return [...s].reverse().join(''); }
        q.push(n); } }
    return null;
  }
}

const solve = (level: string): string => {
  try {
    const m = solveLevel2(level);
    if (m) return m;
  } catch { }
  try { return gsolve(level, 3_000_000); } catch { return ''; }
};

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}

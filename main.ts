// Push-optimal Sokoban solver for make.fun sokoban-solver-01.
// Hallway-row decomposition: each room off the hallway is solved independently
// with a push-optimal A* over (sorted boxes, player region); room plans are
// stitched with player walks. Total pushes = sum of room optima = P*.

import * as fs from "node:fs";
import * as path from "node:path";

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

interface Level {
  w: number;
  h: number;
  n: number;
  wall: Uint8Array;
  goal: Uint8Array;
  box: Uint8Array;
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split("\n").filter((r) => r.length > 0);
  const w = Math.max(...rows.map((r) => r.length));
  const h = rows.length;
  const n = w * h;
  const wall = new Uint8Array(n).fill(1);
  const goal = new Uint8Array(n);
  const box = new Uint8Array(n);
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === "#") continue;
      wall[i] = 0;
      if (ch === "." || ch === "*" || ch === "+") goal[i] = 1;
      if (ch === "$" || ch === "*") box[i] = 1;
      if (ch === "@" || ch === "+") player = i;
    }
  });
  return { w, h, n, wall, goal, box, player };
}

function dirLetter(d: number, w: number): string {
  if (d === -w) return "u";
  if (d === w) return "d";
  if (d === -1) return "l";
  return "r";
}

interface Room {
  cells: number[]; // room floor cells (includes the door cell)
  cellSet: Uint8Array; // over the whole board
  door: number; // room cell adjacent to the hallway row
  hall: number; // hallway-row cell in front of the door
  boxes: number[];
  goals: number[];
}

function findRooms(lv: Level): Room[] {
  const { w, h, wall, goal, box, player } = lv;
  const hy = Math.floor(player / w);
  const seen = new Uint8Array(lv.n);
  const rooms: Room[] = [];
  for (const half of [-1, 1]) {
    for (let y = 0; y < h; y++) {
      if ((y - hy) * half <= 0) continue; // strictly on this side
      for (let x = 0; x < w; x++) {
        const start = y * w + x;
        if (wall[start] || seen[start]) continue;
        // BFS the component
        const cells: number[] = [];
        const stack = [start];
        seen[start] = 1;
        while (stack.length > 0) {
          const c = stack.pop()!;
          cells.push(c);
          for (const d of [-w, w, -1, 1]) {
            const nb = c + d;
            const ny = Math.floor(nb / w);
            if (ny < 0 || ny >= h) continue;
            if (Math.abs(ny - y) > 1 && (nb < 0 || nb >= lv.n)) continue;
            if (nb < 0 || nb >= lv.n) continue;
            if (wall[nb] || seen[nb]) continue;
            if (Math.floor(nb / w) === hy) continue; // hallway row excluded
            seen[nb] = 1;
            stack.push(nb);
          }
        }
        let boxes = 0;
        let goals = 0;
        let door = -1;
        for (const c of cells) {
          if (box[c]) boxes++;
          if (goal[c]) goals++;
          const cy = Math.floor(c / w);
          if (Math.abs(cy - hy) === 1) door = c;
        }
        if (boxes === 0) continue;
        if (door < 0) continue; // not a room off the hallway
        const cellSet = new Uint8Array(lv.n);
        for (const c of cells) cellSet[c] = 1;
        const hall = door + (hy - Math.floor(door / w)) * w;
        const roomBoxes: number[] = [];
        const roomGoals: number[] = [];
        for (const c of cells) {
          if (box[c]) roomBoxes.push(c);
          if (goal[c]) roomGoals.push(c);
        }
        roomBoxes.sort((a, b) => a - b);
        rooms.push({ cells, cellSet, door, hall, boxes: roomBoxes, goals: roomGoals });
      }
    }
  }
  return rooms;
}

const INF = 0x3fff;

// Pull distance from every cell to a given goal, ignoring player reachability
// and other boxes: a lower bound on pushes for one box.
function pullDistances(room: Room, w: number, n: number): number[] {
  const dist = new Int16Array(n).fill(INF);
  const queue: number[] = [];
  for (const g of room.goals) {
    dist[g] = 0;
    queue.push(g);
  }
  // multi-source BFS from all goals at once (min over goals)
  let head = 0;
  while (head < queue.length) {
    const b = queue[head++];
    for (const d of [-w, w, -1, 1]) {
      const a = b - d; // box was at a, pushed in direction d to b
      const p = a - d; // player stood at a - d
      if (a < 0 || a >= dist.length) continue;
      if (!room.cellSet[a] || dist[a] !== INF) continue;
      if (p < 0 || p >= dist.length) continue;
      if (!room.cellSet[p] && p !== room.hall) continue;
      dist[a] = dist[b] + 1;
      queue.push(a);
    }
  }
  return Array.from(dist);
}

interface Push {
  a: number; // box old cell
  b: number; // box new cell
  d: number; // direction
}

interface SearchNode {
  key: string;
  g: number;
  f: number;
  boxes: number[]; // sorted
  player: number; // exact player cell
  parent: SearchNode | null;
  push: Push | null;
}

// binary min-heap on (f, seq)
class Heap {
  private a: SearchNode[] = [];
  private seq = 0;
  get size(): number {
    return this.a.length;
  }
  push(n: SearchNode): void {
    n.key = n.key + "\u0000" + this.seq++; // not used; seq tiebreak via array
    this.a.push(n);
    let i = this.a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (this.less(i, p)) {
        [this.a[i], this.a[p]] = [this.a[p], this.a[i]];
        i = p;
      } else break;
    }
  }
  private less(i: number, j: number): boolean {
    if (this.a[i].f !== this.a[j].f) return this.a[i].f < this.a[j].f;
    return this.a[i].g > this.a[j].g; // deeper first on ties
  }
  pop(): SearchNode | undefined {
    const top = this.a[0];
    const last = this.a.pop()!;
    if (this.a.length > 0) {
      this.a[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < this.a.length && this.less(l, m)) m = l;
        if (r < this.a.length && this.less(r, m)) m = r;
        if (m === i) break;
        [this.a[i], this.a[m]] = [this.a[m], this.a[i]];
        i = m;
      }
    }
    return top;
  }
}

function playerRegion(
  player: number,
  boxes: number[],
  room: Room,
  walk: Uint8Array
): { min: number; reach: Uint8Array } {
  // walk: scratch array over the board; room cells + hall are walkable floor
  const reach = walk;
  reach.fill(0);
  const boxSet = new Uint8Array(reach.length);
  for (const b of boxes) boxSet[b] = 1;
  const stack = [player];
  reach[player] = 1;
  let min = player;
  while (stack.length > 0) {
    const c = stack.pop()!;
    for (const d of [-1, 1]) {
      const nb = c + d;
      if (nb < 0 || nb >= reach.length || reach[nb]) continue;
      if (boxSet[nb]) continue;
      if (!room.cellSet[nb] && nb !== room.hall) continue;
      reach[nb] = 1;
      if (nb < min) min = nb;
      stack.push(nb);
    }
    for (const d of [-room_w(), room_w()]) {
      const nb = c + d;
      if (nb < 0 || nb >= reach.length || reach[nb]) continue;
      if (boxSet[nb]) continue;
      if (!room.cellSet[nb] && nb !== room.hall) continue;
      reach[nb] = 1;
      if (nb < min) min = nb;
      stack.push(nb);
    }
  }
  return { min, reach };
}

let BOARD_W = 16;
function room_w(): number {
  return BOARD_W;
}

function boxesKey(boxes: number[]): string {
  return boxes.join(",");
}

// Push-optimal A* for one room. Returns the push list, or null.
function solveRoom(room: Room, lv: Level): Push[] | null {
  const w = lv.w;
  BOARD_W = w;
  const n = lv.n;

  // per-cell lower bound to nearest goal
  const dist = pullDistances(room, w, n);
  for (const b of room.boxes) {
    if (dist[b] >= INF) return null; // box cannot reach any goal
  }

  const isGoal = lv.goal;
  const blockedScratch = new Uint8Array(n);
  const walkScratch = new Uint8Array(n);

  const blockedForBox = (i: number): boolean => {
    if (i < 0 || i >= n) return true;
    if (lv.wall[i]) return true;
    if (i === room.hall) return true; // never push a box into the hallway
    return !room.cellSet[i];
  };

  const startBoxes = room.boxes.slice().sort((a, b) => a - b);
  const sr = playerRegion(room.hall, startBoxes, room, walkScratch);
  const startNode: SearchNode = {
    key: boxesKey(startBoxes) + "|" + sr.min,
    g: 0,
    f: 0,
    boxes: startBoxes,
    player: room.hall,
    parent: null,
    push: null,
  };
  let h0 = 0;
  for (const b of startBoxes) h0 += dist[b];
  startNode.f = h0;

  const heap = new Heap();
  heap.push(startNode);
  const best = new Map<string, number>();
  best.set(startNode.key, 0);

  let goalNode: SearchNode | null = null;

  while (heap.size > 0) {
    const node = heap.pop()!;
    const bg = best.get(node.key);
    if (bg !== undefined && node.g > bg) continue;
    // goal test: all boxes on goals and player can reach the door
    let all = true;
    for (const b of node.boxes) {
      if (!isGoal[b]) {
        all = false;
        break;
      }
    }
    // snapshot the reachable set for this node's expansion: later
    // playerRegion calls must not clobber it
    const reg0 = playerRegion(node.player, node.boxes, room, walkScratch);
    const reachSnap = reg0.reach.slice();
    if (all && reachSnap[room.door]) {
      goalNode = node;
      break;
    }
    // expand pushes
    const boxSet = new Uint8Array(n);
    for (const b of node.boxes) boxSet[b] = 1;
    for (const a of node.boxes) {
      for (const d of [-w, w, -1, 1]) {
        const p = a - d; // player cell
        const b = a + d; // box destination
        if (b < 0 || b >= n) continue;
        if (!room.cellSet[b] || b === room.hall) continue;
        if (boxSet[b]) continue;
        if (p < 0 || p >= n) continue;
        if (boxSet[p]) continue;
        if (!(p === room.hall || room.cellSet[p])) continue;
        if (!reachSnap[p]) continue;
        const nb = node.boxes.slice();
        const idx = nb.indexOf(a);
        nb[idx] = b;
        nb.sort((x, y) => x - y);
        // dead-box pruning
        if (!isGoal[b]) {
          // corner: two perpendicular blocked sides
          const up = blockedForBox(b - w);
          const down = blockedForBox(b + w);
          const left = blockedForBox(b - 1);
          const right = blockedForBox(b + 1);
          if ((up || down) && (left || right)) continue;
          if (dist[b] >= INF) continue;
        }
        // frozen-box pruning: a NON-goal box is frozen when, on both axes,
        // at least one side is a simple wall (walls never move). Boxes on
        // goals are exempt (they may legally stay put forever).
        if (!isGoal[b]) {
          const wallAt = (c: number): boolean => c < 0 || c >= n || lv.wall[c] === 1;
          const vFrozen = wallAt(b - w) || wallAt(b + w);
          const hFrozen = wallAt(b - 1) || wallAt(b + 1);
          if (vFrozen && hFrozen) continue;
        }
        const nreg = playerRegion(a, nb, room, walkScratch);
        const key = boxesKey(nb) + "|" + nreg.min;
        const ng = node.g + 1;
        const prev = best.get(key);
        if (prev !== undefined && prev <= ng) continue;
        best.set(key, ng);
        let nh = 0;
        for (const bb of nb) nh += dist[bb];
        heap.push({
          key,
          g: ng,
          f: ng + nh,
          boxes: nb,
          player: a, // after the push the player stands on the box's old cell
          parent: node,
          push: { a, b, d },
        });
      }
    }
  }
  if (goalNode === null) return null;
  const pushes: Push[] = [];
  for (let cur: SearchNode | null = goalNode; cur !== null && cur.push !== null; cur = cur.parent) {
    pushes.push(cur.push);
  }
  pushes.reverse();
  return pushes;
}

// BFS walk from s to t over floor cells avoiding boxes. Returns move letters.
function walkPath(
  s: number,
  t: number,
  box: Uint8Array,
  lv: Level,
  from: Int32Array
): string {
  const { w, n, wall } = lv;
  if (s === t) return "";
  from.fill(-1);
  const queue = [s];
  from[s] = s;
  let head = 0;
  while (head < queue.length) {
    const c = queue[head++];
    if (c === t) break;
    for (const d of [-w, w, -1, 1]) {
      const nb = c + d;
      if (nb < 0 || nb >= n) continue;
      if (wall[nb] || box[nb]) continue;
      if (from[nb] !== -1) continue;
      from[nb] = c;
      queue.push(nb);
    }
  }
  if (from[t] === -1) throw new Error("walk: no path");
  // reconstruct
  const seq: number[] = [];
  let c = t;
  while (c !== s) {
    seq.push(c);
    c = from[c];
  }
  seq.reverse();
  let out = "";
  let cur = s;
  for (const nxt of seq) {
    const d = nxt - cur;
    out += dirLetter(d, w);
    cur = nxt;
  }
  return out;
}

function solveLevel(lv: Level): string {
  const { w, n, wall, goal, box } = lv;
  BOARD_W = w;
  const rooms = findRooms(lv);
  const boxNow = new Uint8Array(box); // mutable box layout
  const plans: { room: Room; pushes: Push[] }[] = [];
  for (const room of rooms) {
    const pushes = solveRoom(room, lv);
    if (pushes === null) throw new Error("room unsolved");
    plans.push({ room, pushes });
  }
  // order rooms by hallway column of the door (arbitrary but deterministic)
  plans.sort((x, y) => x.room.hall - y.room.hall);

  const from = new Int32Array(n).fill(-1);
  let player = lv.player;
  let moves = "";

  const roomOfBox = new Map<number, Room>();
  for (const p of plans) for (const b of p.room.boxes) roomOfBox.set(b, p.room);

  for (const { room, pushes } of plans) {
    // walk to the hallway cell in front of the door
    moves += walkPath(player, room.hall, boxNow, lv, from);
    player = room.hall;
    for (const push of pushes) {
      const stand = push.a - push.d; // player must be here to push
      moves += walkPath(player, stand, boxNow, lv, from);
      player = stand;
      moves += dirLetter(push.d, w);
      // push: box moves a -> b, PLAYER STANDS ON THE BOX'S OLD CELL a
      if (!boxNow[push.a]) throw new Error("push: no box at source");
      if (boxNow[push.b]) throw new Error("push: destination occupied");
      boxNow[push.a] = 0;
      boxNow[push.b] = 1;
      player = push.a;
    }
    // walk back out to the hallway
    moves += walkPath(player, room.hall, boxNow, lv, from);
    player = room.hall;
  }

  // sanity: every box on a goal
  for (let i = 0; i < n; i++) {
    if (boxNow[i] && !goal[i]) throw new Error("final box off goal");
  }
  return moves;
}

function main(): void {
  const ids = fs
    .readdirSync(INPUT_DIR)
    .filter((f: string) => fs.statSync(path.join(INPUT_DIR, f)).isDirectory())
    .sort();
  for (const id of ids) {
    const levelText = fs.readFileSync(path.join(INPUT_DIR, id, "level.txt"), "utf8");
    const lv = parseLevel(levelText);
    let solution = "";
    try {
      solution = solveLevel(lv);
    } catch (e) {
      solution = "";
    }
    const outDir = path.join(OUTPUT_DIR, id);
    fs.mkdirSync(outDir, { recursive: true });
    fs.writeFileSync(path.join(outDir, "solution.txt"), solution, "utf8");
  }
}

main();

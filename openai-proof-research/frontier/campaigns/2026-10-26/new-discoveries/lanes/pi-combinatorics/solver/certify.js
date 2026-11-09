#!/usr/bin/env node
// Extract P2's winning strategy from the minimax value function and verify it
// by exhaustive simulation over all P1 play. Certificate is independent of the
// minimax recursion: it only uses legal() and completes() predicates.
'use strict';
const fs = require('fs');
function main() {
  const toks = fs.readFileSync(0, 'utf8').split(/\s+/).filter(s => s.length).map(Number);
  let tp = 0;
  const ni = () => toks[tp++];
  const n = ni(), m = ni();
  const ea = new Array(m), eb = new Array(m);
  for (let i = 0; i < m; i++) { ea[i] = ni(); eb[i] = ni(); }
  const idxOf = new Map();
  for (let i = 0; i < m; i++) { idxOf.set(ea[i] + ',' + eb[i], i); idxOf.set(eb[i] + ',' + ea[i], i); }
  const f = ni();
  const fedge = [], freq = [];
  const efc = new Array(m).fill(0), efl = [];
  for (let i = 0; i < m; i++) efl.push([]);
  for (let i = 0; i < f; i++) {
    const k = ni(); const ed = [], rq = []; const seq = [];
    for (let p = 0; p < k; p++) seq.push(ni());
    for (let p = 0; p < k; p++) {
      const u = seq[p], v = seq[(p + 1) % k];
      const e = idxOf.get(u + ',' + v);
      ed.push(e); rq.push(ea[e] === u ? 1 : 2);
      efl[e].push(i); efc[e]++;
    }
    fedge.push(ed); freq.push(rq);
  }
  const adje = []; for (let i = 0; i < n; i++) adje.push([]);
  for (let i = 0; i < m; i++) { adje[ea[i]].push(i); adje[eb[i]].push(i); }
  const pw3 = [1]; for (let i = 1; i <= m; i++) pw3.push(pw3[i-1]*3);

  function legal(tri, e, d) {
    for (let t = 0; t < 2; t++) {
      const x = t === 0 ? ea[e] : eb[e];
      const out = (t === 0) ? (d === 1) : (d === 2);
      let allmarked = true, same = true;
      for (const fe of adje[x]) {
        const mk = (fe === e) ? d : tri[fe];
        if (mk === 0) { allmarked = false; break; }
        if (((ea[fe] === x) === (mk === 1)) !== out) { same = false; break; }
      }
      if (allmarked && same) return false;
    }
    return true;
  }
  function completes(tri, e, d) {
    for (let q = 0; q < efc[e]; q++) {
      const fid = efl[e][q]; const ed = fedge[fid], rq = freq[fid];
      let cw = true, ccw = true;
      for (let p = 0; p < ed.length; p++) {
        const e2 = ed[p]; const mk = (e2 === e) ? d : tri[e2];
        if (mk === 0) { cw = ccw = false; break; }
        if (mk !== rq[p]) cw = false;
        if (mk !== 3 - rq[p]) ccw = false;
      }
      if (cw || ccw) return true;
    }
    return false;
  }
  const memo = new Map();
  function solve(st) {
    if (memo.has(st)) return memo.get(st);
    let k = 0, t = st; const tri = new Array(m);
    for (let i = 0; i < m; i++) { tri[i] = t % 3; t = (t - tri[i]) / 3; if (tri[i]) k++; }
    const tomove = (k % 2 === 0) ? 1 : 2;
    let best = 3 - tomove;
    for (let e = 0; e < m; e++) {
      if (tri[e]) continue;
      for (let d = 1; d <= 2; d++) {
        if (!legal(tri, e, d)) continue;
        if (completes(tri, e, d)) { best = tomove; memo.set(st, best); return best; }
        if (solve(st + d * pw3[e]) === tomove) { best = tomove; memo.set(st, best); return best; }
      }
    }
    memo.set(st, best); return best;
  }
  const w = solve(0);
  console.log('minimax winner: P' + w);
  const W = w;

  // Extract P2 strategy: at any reachable state with P2 to move, pick a move
  // after which P2 still wins (by solver value), preferring immediate cell win.
  // Then simulate ALL P1 defenses against this fixed strategy.
  const strat = new Map(); // state -> [e,d] winner's response
  function winmove(st) {
    if (strat.has(st)) return strat.get(st);
    let k = 0, t = st; const tri = new Array(m);
    for (let i = 0; i < m; i++) { tri[i] = t % 3; t = (t - tri[i]) / 3; if (tri[i]) k++; }
    const tomove = (k % 2 === 0) ? 1 : 2;
    if (tomove !== W) throw new Error('winner to move expected');
    let mv = null;
    for (let e = 0; e < m && !mv; e++) {
      if (tri[e]) continue;
      for (let d = 1; d <= 2 && !mv; d++) {
        if (!legal(tri, e, d)) continue;
        if (completes(tri, e, d)) { mv = [e, d, true]; break; }
        if (solve(st + d * pw3[e]) === W) mv = [e, d, false];
      }
    }
    if (!mv) throw new Error('no winning move at state ' + st);
    strat.set(st, mv);
    return mv;
  }

  // exhaustive simulation: loser branches over ALL legal moves; winner follows
  // the extracted strategy. Turn determined by k parity.
  let leaves = 0, cellWins = 0, lastWins = 0;
  function sim(st, tri, k, depth) {
    const turn = (k % 2 === 0) ? 1 : 2;
    const opts = [];
    for (let e = 0; e < m; e++) {
      if (tri[e]) continue;
      for (let d = 1; d <= 2; d++) if (legal(tri, e, d)) opts.push([e, d]);
    }
    if (opts.length === 0) {
      const lastMover = 3 - turn;
      if (lastMover !== W) throw new Error(`loser ${3-W} wins by last move at ${st}?`);
      leaves++; lastWins++;
      return;
    }
    if (turn === W) {
      const mv = winmove(st);
      const [e2, d2, winNow] = mv;
      const tri2 = tri.slice(); tri2[e2] = d2;
      if (winNow || completes(tri, e2, d2)) { leaves++; cellWins++; return; }
      sim(st + d2 * pw3[e2], tri2, k + 1, depth + 1);
    } else {
      for (const [e, d] of opts) {
        if (completes(tri, e, d)) throw new Error(`loser can complete a cell at state ${st}!`);
        const tri2 = tri.slice(); tri2[e] = d;
        sim(st + d * pw3[e], tri2, k + 1, depth + 1);
      }
    }
  }
  sim(0, new Array(m).fill(0), 0, 0);
  console.log(`strategy verified: ${leaves} terminal plays, ${cellWins} winner cell-wins, ${lastWins} winner last-move wins, 0 loser wins`);
  console.log(`strategy table size: ${strat.size} states`);
  // dump strategy
  const rows = [];
  for (const [st, [e, d, wn]] of [...strat.entries()].sort((a, b) => a[0] - b[0])) {
    rows.push(`${st} ${e} ${d} ${wn ? 1 : 0}`);
  }
  fs.writeFileSync('p2_strategy.txt', rows.join('\n') + '\n');
  console.log('strategy table written to p2_strategy.txt');
}
main();

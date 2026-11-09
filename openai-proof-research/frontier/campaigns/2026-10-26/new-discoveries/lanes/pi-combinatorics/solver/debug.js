#!/usr/bin/env node
// Debug: print principal variation for a board from stdin.
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
  const flen = [], fedge = [], freq = [];
  const efc = new Array(m).fill(0), efl = [];
  for (let i = 0; i < m; i++) efl.push([]);
  for (let i = 0; i < f; i++) {
    const k = ni(); flen.push(k);
    const ed = [], rq = []; const seq = [];
    for (let p = 0; p < k; p++) seq.push(ni());
    for (let p = 0; p < k; p++) {
      const u = seq[p], v = seq[(p + 1) % k];
      const e = idxOf.get(u + ',' + v);
      ed.push(e); rq.push(ea[e] === u ? 1 : 2);
      efl[e].push(i); efc[e]++;
    }
    fedge.push(ed); freq.push(rq);
  }
  const adjdeg = new Array(n).fill(0);
  for (let i = 0; i < m; i++) { adjdeg[ea[i]]++; adjdeg[eb[i]]++; }
  const adje = []; for (let i = 0; i < n; i++) adje.push([]);
  for (let i = 0; i < m; i++) { adje[ea[i]].push(i); adje[eb[i]].push(i); }
  const pw3 = [1]; for (let i = 1; i <= m; i++) pw3.push(pw3[i-1]*3);

  function legal(tri, e, d) {
    const a = ea[e], b = eb[e];
    for (let t = 0; t < 2; t++) {
      const x = t === 0 ? a : b;
      const out = (t === 0) ? (d === 1) : (d === 2);
      let allmarked = true, same = true;
      for (const fe of adje[x]) {
        let mk = (fe === e) ? d : tri[fe];
        if (mk === 0) { allmarked = false; break; }
        const isout = ((ea[fe] === x) === (mk === 1));
        if (isout !== out) { same = false; break; }
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
  // PV: follow winner's choices
  let st = 0, k = 0;
  const tri = new Array(m).fill(0);
  const w = solve(0);
  console.log('winner: P' + w);
  let moveNo = 1;
  while (true) {
    const tomove = (k % 2 === 0) ? 1 : 2;
    let moved = false;
    // prefer a move that wins for tomove; else any legal move (loser's best resistance)
    let fallback = null;
    for (let e = 0; e < m && !moved; e++) {
      if (tri[e]) continue;
      for (let d = 1; d <= 2 && !moved; d++) {
        if (!legal(tri, e, d)) continue;
        const winNow = completes(tri, e, d);
        const sub = winNow ? tomove : solve(st + d * pw3[e]);
        if (sub === tomove) {
          console.log(`move ${moveNo}: P${tomove} marks edge ${e} (${ea[e]}-${eb[e]}) as ${d === 1 ? ea[e] + '->' + eb[e] : eb[e] + '->' + ea[e]}${winNow ? ' [completes cycle cell, WINS]' : ''}`);
          tri[e] = d; st += d * pw3[e]; k++; moveNo++; moved = true;
          if (winNow) process.exit(0);
        } else if (!fallback) fallback = [e, d, winNow];
      }
    }
    if (!moved && fallback) {
      const [e, d, winNow] = fallback;
      console.log(`move ${moveNo}: P${tomove} (losing) marks edge ${e} (${ea[e]}-${eb[e]}) as ${d === 1 ? ea[e] + '->' + eb[e] : eb[e] + '->' + ea[e]}${winNow ? ' [completes cycle cell]' : ''}`);
      tri[e] = d; st += d * pw3[e]; k++; moveNo++; moved = true;
      if (winNow) process.exit(0);
    }
    if (!moved) { console.log(`no legal moves; last mover P${k % 2 === 1 ? 1 : 2} wins`); process.exit(0); }
  }
}
main();

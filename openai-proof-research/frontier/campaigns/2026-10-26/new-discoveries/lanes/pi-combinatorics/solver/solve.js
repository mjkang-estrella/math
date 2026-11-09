#!/usr/bin/env node
// Exact Game of Cycles solver.
// Rules (Alvarado et al., AMM 2021, arXiv:2004.00776):
//  - board: plane graph + its bounded cells (faces given as cyclic vertex sequences)
//  - move: mark an unmarked edge with an arrow; a move may not create a sink or
//    source (vertex all of whose incident edges are marked and all point the
//    same way). A player must move if possible.
//  - win: first to complete a cycle cell (a listed bounded face whose edges are
//    all marked and cycling consistently); else the player who made the last
//    possible move wins.
// Turn = parity of number of marked edges (P1 marks on even counts).
// Usage: node solve.js [-v] < graph.txt   -> prints "P1" or "P2"
// graph.txt:
//   n m
//   m lines: u v    (0-indexed)
//   f
//   f lines: k v0 ... v_{k-1}  (bounded face, cyclic, consecutive adjacent)
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
  const efc = new Array(m).fill(0), efl = [], efp = [];
  for (let i = 0; i < m; i++) { efl.push([]); efp.push([]); }
  for (let i = 0; i < f; i++) {
    const k = ni();
    const ed = [], rq = [];
    const seq = [];
    for (let p = 0; p < k; p++) seq.push(ni());
    for (let p = 0; p < k; p++) {
      const u = seq[p], v = seq[(p + 1) % k];
      const e = idxOf.get(u + ',' + v);
      if (e === undefined) { console.error('bad face edge ' + u + '-' + v); process.exit(1); }
      ed.push(e); rq.push(ea[e] === u ? 1 : 2);
      efl[e].push(i); efp[e].push(p); efc[e]++;
    }
    fedge.push(ed); freq.push(rq);
  }
  // adjacency
  const adjdeg = new Array(n).fill(0);
  for (let i = 0; i < m; i++) { adjdeg[ea[i]]++; adjdeg[eb[i]]++; }
  const adje = [];
  for (let i = 0; i < n; i++) adje.push([]);
  for (let i = 0; i < m; i++) { adje[ea[i]].push(i); adje[eb[i]].push(i); }

  // powers of 3
  const pw3 = new Array(m + 1);
  pw3[0] = 1;
  for (let i = 1; i <= m; i++) pw3[i] = pw3[i - 1] * 3;

  const verbose = process.argv.includes('-v');

  // legality: marking edge e with direction d creates no sink/source
  function legal(tri, e, d) {
    const a = ea[e], b = eb[e];
    for (let t = 0; t < 2; t++) {
      const x = t === 0 ? a : b;
      const out = (t === 0) ? (d === 1) : (d === 2);
      let allmarked = true, same = true;
      const inc = adje[x];
      for (let i = 0; i < inc.length; i++) {
        const fe = inc[i];
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
      const fid = efl[e][q];
      const ed = fedge[fid], rq = freq[fid];
      let cw = true, ccw = true;
      for (let p = 0; p < ed.length; p++) {
        const e2 = ed[p];
        const mk = (e2 === e) ? d : tri[e2];
        if (mk === 0) { cw = ccw = false; break; }
        if (mk !== rq[p]) cw = false;
        if (mk !== 3 - rq[p]) ccw = false;
      }
      if (cw || ccw) return true;
    }
    return false;
  }

  // memo
  let flat = null, memo = null;
  const total = pw3[m];
  if (total <= 1 << 26) { flat = new Uint8Array(total); }
  else memo = new Map();

  let nodes = 0;

  function solve(st) {
    if (flat) {
      const v = flat[st];
      if (v !== 0) return v - 1;
    } else {
      const v = memo.get(st);
      if (v !== undefined) return v;
    }
    nodes++;
    const tri = new Array(m); // must be per-call: recursion mutates it
    let k = 0, t = st;
    for (let i = 0; i < m; i++) { tri[i] = t % 3; t = (t - tri[i]) / 3; if (tri[i]) k++; }
    const tomove = (k % 2 === 0) ? 1 : 2;
    let best = 3 - tomove;
    for (let e = 0; e < m; e++) {
      if (tri[e]) continue;
      for (let d = 1; d <= 2; d++) {
        if (!legal(tri, e, d)) continue;
        if (completes(tri, e, d)) { best = tomove; break; }
        const ns = st + d * pw3[e];
        if (solve(ns) === tomove) { best = tomove; break; }
      }
      if (best === tomove) break;
    }
    if (flat) flat[st] = best + 1; else memo.set(st, best);
    return best;
  }

  const w = solve(0);
  console.log('P' + w);
  if (verbose) {
    const memoSize = flat ? 'flat' : memo.size;
    console.error(`nodes=${nodes} memo=${memoSize} m=${m} faces=${f}`);
  }
}
main();

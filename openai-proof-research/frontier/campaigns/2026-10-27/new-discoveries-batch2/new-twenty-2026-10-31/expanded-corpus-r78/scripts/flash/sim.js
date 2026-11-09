// Slow Flashcard Game (Lewis-Li arXiv 1210.2419 Sec. 2; NKS12): deck = permutation of
// positive integers; at each step the front card, seen k times so far, moves to position
// p_k = k+1; then the new front card's counter increments. T_i(n) = time card i seen nth time.
// Check Conjecture 3.8: T_i(n+1) - T_i(n) <= 2n for all observed i, n.
'use strict';
const TMAX = +process.argv[2];
const W = 1 << 16; // deck window capacity (positions beyond only hold unseen cards i in order)
let deck = new Int32Array(W); let len = 0; let nextNew = 1; // cards in window; beyond window: nextNew, nextNew+1,...
function ensure(p) { while (len < p) deck[len++] = nextNew++; }
const seen = new Int32Array(1 << 22), last = new Float64Array(1 << 22);
ensure(2); // t=1: card 1 at front, seen once
seen[deck[0]] = 1; last[deck[0]] = 1;
let worst2 = -1e9, worst2Rec = null, worst = -1e9, worstRec = null, maxRatio = 0, steps = 0, maxp = 0, tight = 0;
for (let t = 2; t <= TMAX; t++) {
  const c = deck[0]; const k = seen[c]; const p = k + 1; // move to position p (1-based)
  ensure(p + 1); if (p > maxp) maxp = p;
  deck.copyWithin(0, 1, p); deck[p - 1] = c;
  const f = deck[0]; const n = seen[f]; // n viewings so far; now (n+1)th at time t
  if (n > 0) { const d = t - last[f]; const slack = d - 2*n; if (slack > worst) { worst = slack; worstRec = { card: f, n, d, t }; } if (slack === 0) tight++; if (n >= 2 && slack > worst2) { worst2 = slack; worst2Rec = { card: f, n, d, t }; } }
  seen[f] = n + 1; last[f] = t;
}
console.log(JSON.stringify({ TMAX, cardsSeen: nextNew - 1, maxp, worstSlack_d_minus_2n: worst, worstRec, tightCount: tight, worstSlackForNge2: worst2, worst2Rec }));

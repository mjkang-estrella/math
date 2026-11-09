# MathDB 346238: inequivalence conjecture for GPO/GJPO de Bruijn generation (Chang, Ezerman, Fahreza and Wang)

Source: arXiv:2004.09810. v1 and v2 are cached. The conjecture is Conjecture 1 of v2 (line 1362);
v1 states it at line 816. Both versions say "Computational evidences point to the following
conjecture" and give no verified range.

## Implementation (validated)

`../../scripts/gjpo.py` implements Algorithm 3 (GJPO) as follows. The bars on the
complemented bits were lost in the PDF text and are restored from Remark 1, from the proof of
Lemma 7, and from Example 3.

- The opposite successor is preferred when it has not yet been visited.
- The added assignment c ← (c1, …, c_{n−1}, f(c)) applies when that f-successor is an unused
  tree label. Labels are states w ∈ C_i whose companion (last bit flipped) is a leaf of G_j.
- Tree edges point from each non-root component towards the root.

Validation runs:
- **Example 7** (n = 5, m = 4, h = x0 + x1 + x2 + x3, so n = m + 1, outside the conjecture's
  range) reproduces the source exactly: 32 rooted spanning trees, 128 input pairs and 96
  inequivalent sequences. The multiplicity histogram is 70 × 1, 23 × 2 and 1 each of 3, 4 and 5.
- **Example 3** (`../../scripts/gjpo_example3.py`, log `logs/gjpo-example3.log`) reproduces all
  eight output sequences printed in the source, for both choices of w and all four initial
  states. That includes the source's collisions u = 1110 versus 0111 and 3 inequivalent sequences
  per tree.
- Every run produced a de Bruijn sequence (0 failures).

## Exact coverage (n ≥ m + 2, all nonsingular h = x0 + g(x1..x_{m−1}), every rooted spanning tree, every initial state in the root cycle)

| m | n | h functions | rooted trees | input pairs | collisions |
|---|---|---|---|---|---|
| 1 | 3–7 | 2 | 3 | 4 | 0 |
| 2 | 4–8 | 4 | 8 | 16 | 0 |
| 3 | 5–8 | 16 | 64 | 192 | 0 |
| 4 | 6, 7, 8 | 256 | 3904 | 16896 | 0 |
| 5 | 7 | 65536 | 9295360 | 59070464 | 0 |

The m = 5 run used 37 contiguous capped chunks; see `../../outputs/gjpo-m5-summary.json`.

The counts are independent of n, as Proposition 2 of the source predicts: the PAG of F_h is
the doubled adjacency graph of h. No collision was found. This is a bounded non-finding, not a
proof.

## Proof-route analysis (incomplete)

Fix a run (Δ, u) with output cycle π. For each non-leaf v, its two predecessors 0q and 1q
satisfy two rules:
- the predecessor visited first goes to the leaf ṽ, unless v ∈ E(Δ);
- when v ∈ E(Δ), the predecessor visited first goes to v.

Hence E(Δ) is determined by π together with the start u. A second pair (Δ′, u′) with the same
cyclic output exists iff two conditions hold:
- E(Δ) △ Split(p) is the label set of a rooted spanning tree with root comp(u′);
- u′ = π^p(u) lies in a cycle.

Here Split(p) is the set of (n−1)-windows occurring exactly once among the first p states. The
GJPO run from u′ then follows π step by step; this was checked case by case.

So the conjecture becomes a statement about intervals of de Bruijn cycles that split few
conjugate pairs. The case n = m + 1 (Example 7) shows that the bound genuinely needs
n ≥ m + 2. No uniform proof was obtained, so the item is PARKED.

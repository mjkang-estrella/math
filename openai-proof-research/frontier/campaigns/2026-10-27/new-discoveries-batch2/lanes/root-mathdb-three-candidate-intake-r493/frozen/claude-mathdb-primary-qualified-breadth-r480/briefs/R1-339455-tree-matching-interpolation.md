# R1 — MathDB 339455: retained argument for Conjecture 3.18 of arXiv:1806.02399v1 (NOT a qualified brief)

Retained for separate independent review, as instructed. I classify it as a **routine adaptation**: an explicit classical bridge applies (switching connectivity of connected realizations, R. Taylor 1981, "Constrained switchings in graphs", LNM 884), plus a one-line Lipschitz lemma. Interpolation theorems over degree-sequence realizations are a known genre, so prior coverage is likely (HOLD, unchecked).

## Literal statement
Conjecture 3.18: let s be a tree degree sequence of length n > 2, and T_s the set of (labeled) trees with degree sequence s. Then every k with ν_m(T_s) ≤ k ≤ ν_M(T_s) is realized as ν(T) for some T ∈ T_s.

## Argument
1. **Lipschitz.** Let T' = T − ab − cd + ac + bd be a 2-switch, with both T and T' trees. For a maximum matching M of T:
   - if ab, cd ∈ M, then M − ab − cd + ac + bd is a matching of T';
   - if exactly one of them is in M, removing it gives a matching of size ν−1;
   - if neither is in M, M itself survives.

   So ν(T') ≥ ν(T) − 1, and by symmetry |ν(T) − ν(T')| ≤ 1.
2. **Connectivity of T_s under tree-preserving 2-switches** (self-contained, by induction on n).
   - Take a leaf ℓ of T'. It is also a leaf of T, since degrees are per labeled vertex. Let its neighbours be x in T and x' in T'.
   - If x ≠ x': x' has degree ≥ 2 in T (n > 2). Choose a neighbour y of x' in T that is not on the ℓ–x' path. Switch ℓx, x'y into ℓx', xy.
   - The result is again a tree with the same degrees: xy ∉ T, else there would be a cycle.
   - Now ℓ has the same neighbour in both trees. Delete ℓ and induct; switches in T−ℓ lift back to T.
3. Walking from a minimiser to a maximiser changes ν by ≤ 1 per step, so every intermediate integer is attained. ∎

## Bounded check
`scripts/tree_nu.py` runs over all labeled trees with n ≤ 9 (Prüfer codes). It found no gaps, but the maximum spread there is 1, so the check is **vacuous** as evidence (disclosed).

## Why not qualified
The conclusion follows from a classical switching-connectivity bridge plus a trivial Lipschitz bound, which matches the instruction's routine-consequence exclusion.

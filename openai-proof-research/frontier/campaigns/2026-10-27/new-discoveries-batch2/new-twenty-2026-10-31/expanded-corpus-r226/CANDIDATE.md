# No eligible candidate

No new exact solution or Lean packet survives this bounded pass. All 20 records have zero accepted credit. Nine are excluded from this lane; eleven are parked. Root adjudication and independent review are not claimed.

The strongest initially tractable route, **363419**, is already publicly proved. At Omega head `82ca796fa3d326df95fef9758103880b5987a5bf`, `D5/S3/FiniteGroups/BajnokBeattyAllRegimes.lean` states:

```lean
theorem result (k s : ℕ) (hk : 0 < k) (hs : 0 < s) :
    (∃ a b : ZMod 2 × ZMod (2*k), a ≠ b ∧ ∀ g, ∃ x y : ℤ,
      g = x • a + y • b ∧ |x|+|y| ≤ (s : ℤ)) ↔
    (Odd s ∧ 2*k ≤ s^2-1) ∨
    (Even s ∧ 2*k ≤ s^2-s) ∨
    (s%4=0 ∧ Even k ∧ s^2-s < 2*k ∧ 2*k ≤ s^2) ∨
    (s%4=2 ∧ k%4=2 ∧ s^2-s < 2*k ∧ 2*k ≤ s^2)
```

Namespace: `D5.S3.FiniteGroups.BajnokBeattyAllRegimes`. The source file and its proof were read at the pinned public revision; no local rebuild or axioms audit is asserted. The blueprint integration commit is `fc30515347311f7298bb12b6f18c6955fef42c49`, dated 2026-11-02, before this lane. [Public source](https://github.com/the-omega-institute/trureturing/blob/82ca796fa3d326df95fef9758103880b5987a5bf/D5/S3/FiniteGroups/BajnokBeattyAllRegimes.lean). Its arbitrary-pair quantifiers and all four strict/non-strict clauses match the reservation. The finite searches therefore earn no discovery credit.

**363437** remains an unresolved research route after two rounds at different orders using the same exact bundle-count solver. In a bundle of multiplicity m, choosing x outward edges realizes every integer x in 0..m. Processing vertices fixes their final out-degree, and passes m-x contributions to later vertices. This enumerates possible orientations exactly, without enumerating identities of parallel edges. Pruning only removes vertices whose remaining interval cannot meet the allowed set. All maximal forbidden lists suffice because every smaller list is contained in one. The known Euler-tour balanced orientation shortcut does not address a list forbidding both central out-degrees. No general replacement argument or counterexample was found. A finite obstruction would have moderate Lean cost, but no certificate is presently available.

**363027**: exact minimax reproduces the known n=3 and n=5 cases; no odd n>=9 was solved. State `(mask,cur,opp)` tracks the shared unused edges and the two token positions. A legal move changes to `(mask^edge,opp,newcur)`; an empty legal move set loses. The second player's opening is separately enumerated, since their initial token position is not fixed by the first player's move. No claim of new computational range is made.

**363595** has an elementary literal failure: C5 is 1-far from bipartite, has no triangle, and has spectral radius 2. Since T5,2=K2,3 has radius sqrt(6)<3, the conjectured right side is 5(3-sqrt(6))/6>0. The radius of C5 follows from its constant row sum and the infinity-norm upper bound; its maximum cut has four edges. This is a classical five-vertex formulation correction under the task's substantive exclusion rule. It is quarantined, not promoted as a new significant solution. Full cited-example novelty clearance was not completed; no formalization is justified.

Protected spider-family 352905 was not taken over. The general spider record 363023 needs an independent general-n mechanism; n=1 and n=2 are already in the source. The Hermitian, Artin, symmetric-function, analytic and semialgebraic targets retain the specific obligations in results.json. No dummy Lean endpoints were generated.

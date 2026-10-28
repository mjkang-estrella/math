# progress.md — pi-weighted-bw-case-i-r4 (2026-10-28, session log)

Agent: pi (GLM-5.3-Flash), thinking=high, solo (no delegated tasks, no subagents).

1. **Registry & sources (13:00–13:10).** Read batch AGENTS.md/ledger, root record
   `root-weighted-bw-screen-r22/public-case-ii.md`, prior lane `pi-matrix-discovery-r3` discovery/progress.
   Re-fetched trureturing dev record via GitHub API — hash identical to pinned (6aab5f66…); line 79 confirms
   case (i) open. MathDB 362175 live: open, no solutions, lean_formalization_count 0. Saved both to sources/.
   Fetched arXiv 2403.04199v2 HTML; extracted Conjecture 1, Eqs. (14)/(15)/(16), eigenvalue notation, n=2
   identity (19). Fang–Cheng: one ScienceDirect attempt → HTTP 403, logged, no retry (novelty gate remains).
2. **Reduction & n=2 (13:10–13:30).** Fixed the X=A√ω, Y=B√ω, W=ω^(−1/2) reduction; verified paper identity
   (19) on 200 centered pairs (2e-14). Symbolic n=2 work (symb_n2*.py) — first attempt had a sequential-
   substitution conjugate bug, fixed with xreplace. Result D4: n=2 identity holds for ALL pairs, no centering.
3. **Sharpened form (13:30–13:40).** Formulated deficit inequality ‖T‖²+c²|⟨X,Y⟩|² ≤ c²‖X‖²‖Y‖²; verified
   (verify_sharpened.py): min eig of c²‖X‖²I − c²|x⟩⟨x| − T*T ≥ −2e-12 over 400 X (n ≤ 6); bilinear
   superoperator ratio max 0.993.
4. **Wedge structure (13:40–14:10).** Derived T_ij = Σₖ wₖ(X∧Y)_{(ik),(kj)} (D1); verified. Computed ‖Λ‖ on
   the full exterior square with exact rational weights: strictly > c² for n ≥ 3 (D2) — decomposability
   essential. Derived the exact per-(i,j) Lagrange decomposition and the Plücker conversion; identified the
   factor-n obstruction (§5 of SUMMARY.md).
5. **Rank-one and 2-sparse SOS (14:00–14:15).** symb_n3.py: explicit SOS for X = E_pq (D5) and four 2-sparse
   families (D6). One arithmetic slip during hand-check of ‖T(X,E_ab)‖² (used ‖x⁽ᵃ⁾‖² = 1 instead of 5) was
   caught by direct recomputation; final formulas verified against the γ-analysis entry by entry.
6. **Adversarial sweep (14:10–14:25).** final_sweep.py at n = 6/8/12, five family types: max ratio 0.849 —
   no violation; worst family = top-2 leak (consistent with D5 extremal).
7. **Write-up (14:25–14:35).** SUMMARY.md, discovery.md, provenance.json. No PROOF.md (no proof); no Lean
   artifacts (nothing to formalize yet — per batch rules Lean is required only for a found proof).

Time/memory constraints respected: all jobs « 512 MiB, bounded loops, no unbounded searches, no polling of
other lanes' tasks.

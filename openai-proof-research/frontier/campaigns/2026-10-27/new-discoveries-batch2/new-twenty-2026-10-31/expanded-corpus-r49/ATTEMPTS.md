# Sustained routes and attempts (r49)

## Route A — 355956 Yip maximal subfield clique (COUNTEREXAMPLE, Lean PASS)
Primary read: arXiv:2209.00864 source (Conj. 1.1, Thm 1.2 with hypothesis q>(n−1)^2, Prop./proof, sharpness Remark);
ALCO 2023 published TeX (same conjecture; abstract still says "confirms a conjecture of Yip"; remark: "we conjecture that
the condition q>(n−1)^2 can be dropped ... verified n ≤ 5 for q ≤ (n−1)^2, and q ≤ 17 for n = 6"); original
arXiv:2101.09652 Conj. 1.4 (identical wording); follow-up arXiv:2403.04312 (Martin–Yip, no counterexample, cites Thm 1.2
as is); arXiv:2505.04061 abstract only.
Mechanism: Yip's own reduction (extension ⇔ x with x−a ∈ S for all a ∈ F_{p^r}); heuristic count q/d^{p^r} is large exactly
when p^r is tiny and n large, i.e. outside Thm 1.2. Exact exhaustive search (`scripts/yip_fast.py`, log tables over a
primitive modulus, validated against an independent polynomial-power implementation `scripts/yip_search.py` on 81, 25, 9,
6561) over all 26 fields q ≤ 5·10^6 having an admissible case with p^r ≤ (n−1)^2: 219 cases, single failure q=5^8, d=3,
r=1, 960 extension vertices. Interesting non-failure: q=3^8, d=8 (heuristic 12.8, observed 0).
Formal: literal conjecture over all finite fields; refuted for every field of order 5^8; root of f obtained by a
Frobenius certificate + splitting of X^|K|−X (no irreducibility proof needed); cube roots by integer certificates.
Remaining: independent fidelity and significance review; worldwide prior-art beyond the bounded search below.

## Route B — 355701 v3 configuration partial converse (COUNTEREXAMPLE, Lean PASS)
Primary read: arXiv:2208.06912 source (definitions §2.2 incl. "purely combinatorial", triangle Def., Thm 6.1, Cor., both
examples, Conjecture) and published EJGTA 11(2) 2023 PDF (Conjecture 1 identical). Mechanism: random generation of n_3
configurations (n = 9..20) with exact clique number and exact 2-colorability backtracking; validated on Fano (min 4),
Pappus (ω=3, min 0) and source example 1 (ω=5, min 0). Independent brute-force verifier confirms a 9_3 counterexample
(ω=4, min 1). Source example 2 is not a symmetric v3 configuration (point 1 lies on 4 lines) — noted, not used.
Formal: literal statement over arbitrary finite point types, both "inclusion-maximal" and "maximum" readings refuted.
Remaining: independent fidelity and significance review (the counterexample is very small; the source checked only
Fano, Young, Möbius–Kantor, Pappus, Desargues).

## Route C — 355748 promotion noninvertibility (diagnostic only)
Primary read: arXiv:2208.08665 §1.1 extended promotion definition, Thm (rooted trees ≥ n), Conjecture.
Exact exhaustive computation over all naturally labeled posets: n ≤ 6 (4824 posets at n=6): max deg(∂) equals
(n+1)(n+2)/6 (attained by the chain; uniqueness of the maximizer not checked); no counterexample. Reformulation used: |∂^{-1}(M)| equals
the number of chains v1<…<vm = M^{-1}(n) that are promotion chains of the reconstructed labeling (successor-minimality
conditions). No proof found; n=7 (≈9.6·10^4 natural posets × 5040) not run within budget. PARKED.

## Literal-defect findings (no credit)
- 355892: C_7 (Δ=2) has semistrong chromatic index 4 > Δ^2−1 = 3 (exact, `logs/defect-checks.json`); K_1 also fails.
  The Δ=3 case follows from the source theorem `thm:cubic` (connected, Δ=3, ≠K_{3,3} ⇒ ≤ 8), so the conjecture's content is Δ ≥ 4: domain correction, zero.
- 355617: the source's own Theorem (Lah formula) gives χ̃(X(K_3)) = −1 < 0 = χ̃ of a one-edge digraph; the stated
  inequality fails trivially for n=3,4,6,8 against the empty or one-edge digraph; the intended statement is presumably
  |χ̃|. Wording correction, zero; the corrected question is a different (non-literal) problem, not attempted.

### Route B search statistics (seed 49001, 1200 CPU-s, random labeled samples, not iso-reduced)
ω=4 and non-2-colorable samples occurred at n = 9 (118081 of 238600 ω=4 samples), 11 (845) and 13 (3); none at n = 10, 12,
14–20 among ω ≤ 4 samples. Only the n = 9 instance is certified (brute force + Lean); the others are unverified diagnostics.

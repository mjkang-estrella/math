# progress.md — pi-jacobi-shifted-content-discovery (2026-10-27)

Solo lane, no children, Pi GLM5.3Flash. Own directory only; parent lane read-only.

## Work log

1. Read AGENTS.md, ledger.json (tally 22/30), parent lane STATUS.md; read the full
   source paper 2608.23006v2 (Definition 2.1, Theorems 1.1–1.5, §2–5, Remark 3.8,
   Computational observation 3.1) and the companion 2609.29531 (§§1, 7.1–7.7, 8, 9
   header, 10, 11, App. A header).

2. Re-derived the parent reduction analytically:
   - amplitude double series with P_l(w) = ∏_{j<l}(w − j(j+1)); settled the sign
     (the two (−1)-layers cancel) and the p↔q convention (parent's script is the
     conjugate; Im flips sign, contents unchanged);
   - [Z^{−n}]F via complete-homogeneous h_{n−c−d}(1..c+d); classical identity
     h_{n−s}(1,…,s) = S2(n,s) proved/machine-checked ⇒ A_n = Σ_m S2(n,m)2^{n−m}(n!/m!)C̃_m;
   - cumulant recursion for B_n (checked against n a_n = Σ k b_k a_{n−k});
   - δ_r = 2r+ν2((r−1)!) ⟺ min ν2(Im B_{2m+1}) = 3m (m = r−1), via
     ν2((2r−1)!) = 2r−2−s2(r−1).

3. Built an independent exact pipeline (`jacobi_shifted_core.py`); validated against
   all published data: den κ_1..κ_4 (4, 96, 7680, 86016 = 2^12·21) and
   ℓ_1..ℓ_4 (1/4, −7/96, 781/7680, −28421/86016).

4. Extended exact verification (N = 83):
   - content law min ν2(Im B_{2m+1}) = 3m for r ≤ 40 (parent: r ≤ 12);
   - top-layer identification with explicit γ_r = 2C(2r,r)/((2r−1)16^r)
     (= C(2r−1,r−1)/((2r−1)2^{4r−2}), re-derived; matches arXiv HTML) for r ≤ 40
     (source: r ≤ 20) — so attainment holds numerically through r = 40;
   - mod-2 unit law Im B_{2m+1} ≡ 2^{3m}[(u+v)^{m+1} + δ_{m≡1(4)}(u+v)^m]
     (mod 2^{3m+1}) for m ≤ 30 — new conjecture implying the full law;
   - Im B_{2k} ≡ 0, deg B_n = ⌈n/2⌉ (n ≤ 83); [u^n]A_n = (1+i)^n (n ≤ 83).

5. Mechanism probing:
   - proved content(Im C̃_s), content(Re C̃_s) ≥ ⌊s/2⌋ ⇒ content(Im A_{2m+1}) = m with
     minimum on the top homogeneous part (verified m ≤ 12): the cumulant recursion
     lifts content m → 3m; the difficulty is exactly the global cancellation.
   - tested an off-diagonal Z+4 difference equation (`test_difference_equation.py`):
     diagonal case reproduces companion Cor. 1.2 exactly, ((Z+1)²−4A)v²; off diagonal
     the coefficients are non-real and non-terminating ⇒ no rational Z-shift relation;
     consistent with the companion's three-term parameter relation (Thm 7.1(35)).
   - studied the closed form (37)–(38): for β ≠ 0 the split blocks at 1/2 and −1 are
     not Gauss/Kummer summable ⇒ the companion's zero-balanced isolation argument does
     not extend verbatim. No bivariate analogue of the explicit F̂_Γ exponential found.

6. Novelty screen: full read of relevant sections; web search (Exa, 3 query angles)
   found only the two source papers and mirrors. No subsuming theorem. The source's
   γ_r decoded from the arXiv HTML matches my derivation.

## Outcome

No all-order theorem. Deliverables: verified reduction; verification ranges r ≤ 40
(law and attainment), m ≤ 30 (mod-2 unit law); structural laws; precise endpoint
(Theorems A+B, equivalently the mod-2 unit law) and Lean plan; honest obstacle map.
**Credit 0 under the counting standard** — nothing here is an accepted discovery.
No PROOF.md written.

## Next steps (for a future session)

1. Prove the mod-2 unit law. Most promising: lift the C̃_s/A_n/B_n chain to closed
   congruences mod 2^k (the [u^n]A_n = p^n and content(Im A_{2m+1}) = m facts fix the
   top terms; the needed precision on Im B_{2j+1} grows with m — a Dwork-style
   induction may close it).
2. Or prove Theorem A directly via a bivariate analogue of the companion's isolation
   (needs the missing explicit exponential).
3. Or prove the top-layer identification (Prop 3.1) all-order via the layer expansion
   (Cor. 8.2) — it is a statement about the degree-(2m+1) part of Im L_{2m+1}.

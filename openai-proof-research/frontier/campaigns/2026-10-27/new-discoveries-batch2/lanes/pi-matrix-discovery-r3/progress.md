# Lane progress — pi-matrix-discovery-r3 (batch 2, solo Pi, no children)

Read first: openai-proof-research/AGENTS.md, batch2 AGENTS.md, batch2 ledger.json,
prior-campaign-context.json, astra-algebra-matrix-r2/SUMMARY.md,
astra-algebra-matrix-r1/progress.md, pi-algebra-matrix-r1/progress.md,
first-campaign lanes parent-matrix-screen-r4/r5, parent-matrix-r6-integration/DECISION.md,
parent-matrix-screen-r7/REVIEW-DECISION.md, pi-matrix-discovery-r6/discovery.md.

## Excluded targets (prior lanes, respected)

- 372905 Clarkson: publicly refuted p=9/4 (trureturing); p=2.5 optimizer artifact. Dead.
- 352327 matrix Shapiro (Choudhury-Sivakumar Conj 2.9): PRIMARY target of active lane
  pi-algebra-matrix-r1. Not mine; no duplication.
- 332493 Banica-Nechita: actively complete, formal under review. Dead.
- 369147, 332318, 322910, 371345/46/47, 375999, 371031, 332939, 344947...: all resolved/stale per
  first-campaign screens. 372787/372585/352819/372716 stale per astra-algebra-matrix-r2.
- 343202 (inverse eigenvector products), 377365 (primitive integer powers): only preliminary
  screens exist; possible fallback targets.
- 361692-96 (Lu-Wenzel/DDVV-type): the survey uses the FROBENIUS norm on X (verified in
  2402.01085 text); the trivial diag(1,-1) "counterexample" fails intended hypotheses.
  Deep open conjectures equivalent to fundamental LW conjecture; high risk.

## Selected target: MathDB 362175 — weighted Frobenius commutator bounds

Source: Aina Mayumi, Gen Kimura, Hiromichi Ohno, Dariusz Chruscinski,
"Bottcher-Wenzel inequality for weighted Frobenius norms and its application to quantum
physics", arXiv:2403.04199 = Linear Algebra Appl. 700 (2024) 35-49,
DOI 10.1016/j.laa.2024.07.013. Conjecture 1 (their eqs (14),(15),(16)):

For positive definite omega, lambda_1 <= ... <= lambda_n eigenvalues, ||A||_omega^2 :=
tr(A* A omega):

 (14) ||[A,B]||_omega <= sqrt((lam_m + lam_sm)/(lam_m lam_sm)) ||A||_omega ||B||_omega
 (15) ||[A,B]||_omega <= sqrt((lam_m + lam_M)/lam_m) ||A||_omega ||B||
 (16) ||[A,B]|| <= sqrt((lam_m + lam_sm)/(lam_m^2 lam_sm)) ||A||_omega ||B||_omega

Proven in source: n=2 all cases; special cases (A normal commuting with omega; B
commuting with omega for (15); B = |lam_1><lam_n| for (15)). Tightness examples known.

CRITICAL prior-art: Fang & Cheng, "On some conjectures concerning the Bottcher-Wenzel
inequality for weighted Frobenius norms", Linear Algebra Appl. 718 (2025) 1-13,
DOI 10.1016/j.laa.2025.03.015 (CLOSED ACCESS; no arXiv; no OA copy found via S2/OpenAlex/
UM repository 2026-10-27). zbMATH review 1564.15017 (reviewer Tin Yau Tam, read from
api.zbmath.org) states they prove (1)=(14), (2)=(15), (4)=(16) FOR RANK-ONE X,Y only,
constants in (1),(2) optimal; sharp constant for (4) left open challenges. So the general
all-matrix case of (14)/(15)/(16) was still open after that paper. (Access limit recorded.)

## Key reduction (my derivation)

With W := omega^{-1/2} = diag(w_1 >= w_2 >= ... >= w_n > 0), w_i = 1/sqrt(lambda_i), and
X := A sqrt(omega), Y := B sqrt(omega): conjecture (14) is EXACTLY equivalent to

 (*) || X W Y - Y W X ||_F <= sqrt(w_1^2 + w_2^2) ||X||_F ||Y||_F  for all X,Y.

(15) reduces to ||X W Y - Y X||_F-type mixed form; (16) similar. Rank-one X attains
sqrt(w_1^2+w_2^2) exactly (T_X = L_{XW} - R_{WX} has norm sqrt(w_q^2+w_p^2) for X = E_pq,
maximized at {p,q}={1,2}), consistent with Fang-Cheng rank-one optimality.

## Plan

1. Numerical optimization of sup_X ||L_{XW} - R_{WX}||_F / ||X||_F for varied W, n=3..8.
2. If violation: exact rational/algebraic witness + certification => refutation of 362175.
3. If no violation: attempt full proof of (*); that would resolve the open conjecture.
4. Save all scripts/receipts in lane; hashes in provenance.

Credit requested: 0 so far (no acceptance). All writes confined to this lane.

## End-of-run state (solo, no children)

- Selected target: MathDB 362175 (weighted Frobenius commutator bounds). Exact
  source read; Fang-Cheng 2025 follow-up scoped via zbMATH review (rank-one
  only; general case open); body closed access - recorded gate.
- Derived exact reduction to (*) ||XWY - YWX||_F <= sqrt(w1^2+w2^2)||X||_F||Y||_F;
  verified numerically (6000 random trials + 30-cell optimization sweep,
  scripts/final_sweep.py, verification/sweep14.json): sup == conjectured
  constant everywhere, extremals always top-2-block supported. No violation.
- Five proof routes attempted and documented as not closing (discovery.md 1.5).
- MathDB 343202 shown equivalent to the real polarization problem (both
  directions, with the Euler-identity and sign-transfer arguments) - recorded
  as a structural clarification; not a session-viable target.
- 377365 glanced only (Diophantine hardness); other matrix targets screened out
  per prior-lane exclusions (see discovery.md Section 2 list).
- Deliverables: SUMMARY.md, discovery.md, provenance.json (URLs+sha256),
  verification/sweep14.{json,log}, two scripts. Credit requested: 0.

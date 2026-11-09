# Sustained lead: odd diagonal Padé reciprocal positivity

**Status: unresolved here; zero nomination, zero credit.** Primary question binding: Scardino, arXiv:2610.39051v1, pp. 2–3 and conclusion p.18, expressly retains the diagonal case after refuting unrestricted Fasi–Higham positivity. Let m be any positive odd integer,

    q_m(z) = sum(j=0..m) (-1)^j binom(m,j) (2m-j)!/(2m)! z^j,
    1/q_m(z) = sum(n>=0) c_n(m) z^n.

The retained question is c_n(m)>0 for every such m and every integer n>=0. This is not the unrestricted all-(k,m) conjecture, now publicly refuted in the same body. The 2019 Fasi–Higham journal body and Grosswald's 1978 Bessel-polynomial monograph were not obtained; their bibliography entries in Scardino do not count as proof-body comparison. No literature novelty PASS is asserted.

## Mechanism 1: formal-series positivity and exact recurrence

With w_j=(-1)^j binom(m,j)(2m-j)!/(2m)!, multiplication gives c_0=1 and c_n=-sum(j=1..min(m,n))w_j c_(n-j). Mixed signs prevent induction from coefficient positivity alone. The source's k=0 argument is genuinely stronger than mere induction: it writes 1/q_(0,m)=exp(z)/(1-F_m(z)) for odd m with F_m coefficientwise nonnegative and zero constant term. It proves the k=0 question immediately by the geometric series, but diagonal k=m is outside it.

A natural diagonal analogue is to multiply q_m by exp(z/2), since w_1=-1/2. It cannot have the form 1-F with F coefficientwise nonnegative: at m=3 the z^2 coefficient is -1/40 while the z^4 coefficient is +1/1920. Hence that proposed positive-series factorization fails, and its failure is preserved in `checks/exact-controls.json`. This is failure of a proof route, not a refutation of the diagonal question.

Exact rational controls, guarded under the requested caps, check every odd 1<=m<=41 and every 0<=n<=240. All 5,061 coefficients are positive; each truncated convolution with q is independently checked to equal 1 through degree 240. This is bounded evidence only. Three source-published non-diagonal negatives are reproduced exactly, to check that the recurrence detects the already-known failure rather than silently assuming positivity. Neither controls nor their recurrence are new discoveries.

## Mechanism 2: pole dominance and the finite-prefix objection

Read the actual partial-fraction proof in Lemma 8.1 and Theorem 8.2/Proposition 8.3 (PDF p.13 and following). For simple zeros zeta_j set R_j=-1/(zeta_j q'(zeta_j)). Then c_n=sum_j R_j zeta_j^(-n). Under source Property D1, the positive zero R is uniquely smallest in modulus and its residue coefficient R_1 is positive. If rho=min(other |zeta_j|)>R and B=sum(other |R_j|),

    c_n >= R^(-n) (R_1-B (rho/R)^(-n)).

Choosing n>=ceil(max(0,log(2B/R_1)/log(rho/R))) proves the positive tail, exactly as the source already does. This is a complete routine bridge conditional on D1, not a new all-n result. Even proving D1 at one diagonal m and checking its finite prefix would only instantiate this explicit closest test. That objection is decisive before allocating substantial computation.

For all odd m, a uniform diagonal D1 proof plus uniform control of the initial segment remains absent. Theorem 7.1 instead fixes m and takes k sufficiently large; its unknown K_m cannot be replaced with k=m. The transient theorem also fixes m as k grows, so the Hermite profile cannot be substituted into the moving-m diagonal regime. We did not run floating-point root searches or relabel a finite m as the full question.

## Chronology, deduplication and next gate

The source feed records v1 submitted 2026-10-28T23:28:52Z with equal updated timestamp; the body already contains all three finite negatives. Current bounded arXiv searches for Fasi+Higham and Bessel-polynomials+positivity were frozen on 2026-10-30 before inspection (`successor-search/`); they provide a narrow discovery check, not a universal absence certificate. The Fasi+Higham query returned this exact v1 and two unrelated Sylvester papers. Search metadata is not proof-body clearance of the other hits. Campaign exclusions are administrative snapshots; this target was not selected from their candidate list.

Precise remaining gaps: full uniform diagonal proof or one exact diagonal counterexample; actual 2019 and closest Bessel positivity bodies; complete comparison with any successor; and authorized lawful current-public-registry evidence. The registry denials remain parked. No ranking, current-novelty PASS, PROOF.md, Lean endpoint or manuscript is supplied.

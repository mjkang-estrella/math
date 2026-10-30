# Miyamoto full quotient ordering: unresolved, credit 0

Research: 2026-10-29 UTC; workspace local date 2026-10-28. Assigned lane only. No nomination, acceptance authority, Lean, git, children or external mutations. Counts remain 3/30 additional, 33/60 total.

## Literal source and actual theorem comparison

Target: Roland Miyamoto, arXiv:2402.06618v2, Conjecture 1, https://arxiv.org/html/2402.06618v2 . Set h_0=1, h_(n+1)=T h_n, k_n=integral h_n, d_n=k_n-k_(n+1), theta_n=d_n/d_(n-1). The FULL target is

    theta_(2m)<theta_(2m+2)<theta_(2m+3)<theta_(2m+1), every integer m>=1.

Theorem 1(b) and its chain-rule/integration proof give polynomial parametrizations; Proposition 2 is explicitly CONDITIONAL on Conjecture 1. Neither finite iterates nor this conditional acceleration is a proof of the conjecture. Source v2 dates to 2024-04-18 (v1 2024-02-09), as recorded in the predecessor's actual abstract receipt.

Companion https://arxiv.org/html/2404.11455v2 (2024-09-05): actual §3 crossing-number definitions, Lemmas 3.2–3.3, Theorem 3.4 and its proof, Proposition 3.5, Theorem 4.1 proof, Corollary 4.2, Stride Lemma 4.3, Corollary 4.5, Hammock Lemma 4.6, Theorems 4.9/4.11 and Proposition 4.12 were consulted. Its domination means g<=f AND supremum over all positive horizontal/vertical rescalings of their sign-switch count equals TWO. It is not ordinary pointwise order. Theorem 3.4 preserves this domination under I and T by tracking sign switches through differentiation, inversion and scaling. Canonical pairwise domination and strict area descent follow. Corollary 4.5 proves k_n/k_(n-1) strictly increases to 1: these are NOT the theta_n. Global convergence and the Hammock lower bound do not give the required four-iterate determinants. No contradiction of this source domination is asserted.

Newly screened same-author follow-up: Claes–Miyamoto, https://arxiv.org/html/2602.10992v1 , dated 2026-02-11. Introduction, actual §5 and Conjectures 5.1/5.2 read: these concern discrete golombic/Levine sequences and multivariate polynomial degrees; 5.1(b) itself conjectures a discrete ratio limit equal to kappa. This is a different sequence and supplies no continuous gap-quotient ordering. Not all theorem proofs in this follow-up were read; no exhaustive non-subsumption claim. Author publication page https://roland.miyamoto.casa/ fetched successfully and lists these three preprints plus the 2023 chapter. No additional continuous quotient proof was found on that page.

## Re-derived sign directions

Since d_j>0 (source strict descent),

    theta_(n+2)-theta_n = A_n/(d_(n+1)d_(n-1)),
    theta_(n+1)-theta_n = C_n/(d_n d_(n-1)),
    A_n=d_(n+2)d_(n-1)-d_n d_(n+1),
    C_n=d_(n+1)d_(n-1)-d_n^2.

The three adjacent links in the literal chain require, respectively,
A_(2m)>0, C_(2m+2)>0, A_(2m+1)<0. These directions were re-derived, not inferred from a cached label. The Fubini identity k_(n+1)=S_n/(2k_n), S_n=integral h_n^2, gives d_n=(2k_n^2-S_n)/(2k_n), as in the previous lane; it alone gives no sign of A or C.

## Exact nonlinear divided-difference reduction

This is an elementary, uncredited identity, NOT a full conjecture proof. It explicitly retains the normalization which prevents positive-kernel shortcuts.

For f>=g continuous strictly decreasing normalized endpoint functions, write k_f=integral f, delta=integral(f-g)>0, p=(f-g)/delta. Layer-cake/Fubini gives

    N_f(x):=integral_x^1 f^{-1}(y)dy = integral_0^1 (f(t)-x)_+ dt.

Proof: integrate the indicator of x<y<f(t) first in y and then t; all integrands are bounded nonnegative. Define

    W_(f,g)(x,t)= [(f(t)-x)_+-(g(t)-x)_+]/[f(t)-g(t)]

where f(t)>g(t), and define W arbitrarily between 0 and 1 where the denominator vanishes. This choice does not affect integrals against p. Equivalently W=integral_0^1 1_{x<g(t)+s(f(t)-g(t))} ds almost everywhere. Therefore

    B_(f,g)(x)=integral p(t) W_(f,g)(x,t)dt=(N_f(x)-N_g(x))/delta,
    Tf(x)-Tg(x)=delta/k_f [B_(f,g)(x)-Tg(x)].                 (1)

To check (1), use N_g=k_g Tg and k_f-k_g=delta. It follows without any differentiability or inverse-derivative assumption.

Apply this to f=h_n,g=h_(n+1), n>=1, and put

    p_n=(h_n-h_(n+1))/d_n, integral p_n=1, p_n>=0,
    H_n=h_(n+2), B_n=B_(h_n,h_(n+1)).

Then the literal canonical recursion is

    theta_(n+1)=(integral B_n-k_(n+2))/k_n,
    p_(n+1)(x)=[B_n(x)-h_(n+2)(x)]/[k_n theta_(n+1)].        (2)

Source domination ensures the numerator in the second line is nonnegative FOR THIS ORBIT. But B_n alone is a positive kernel; its centered version in (2) is not automatically a positive operator on arbitrary inputs. In particular rewriting

    B_n(x)-H_n(x)=integral p_n(t)[W_n(x,t)-H_n(x)]dt

exhibits both signs in the kernel for any interior x: near t=0, W_n=1 and near t=1, W_n=0, while 0<H_n(x)<1. This rules out treating this centered kernel as an ordinary nonnegative Markov kernel. It does not rule out a specialized cone invariant involving the whole orbit.

Integrating W in x gives (f+g)/2: for f>g, integrate the displayed positive-part divided difference, obtaining (f^2-g^2)/(2(f-g)). Hence, with

    R_n=integral (h_n+h_(n+1))p_n / (2k_(n+1)),

one gets the simpler exact scalar identity

    R_n=1+theta_(n+1).                                    (3)

For completeness an algebraic proof avoids solving the implicit expression obtained by integrating (2): set k=k_n,d=d_n,b=integral h_n p_n,c=integral p_n^2. Since S_n=2k(k-d),

    S_(n+1)=S_n-2db+d^2c,
    d_(n+1)/d_n=(b-dc/2)/(k-d)-1=R_n-1.

All integrals exist because each fixed p_n is bounded and d_n>0. This also independently checks normalization and directions.

Thus the exact unresolved inequality is

    R_(2m-1)<R_(2m+1)<R_(2m+2)<R_(2m), for every m>=1,    (4)

where BOTH h_n and p_n obey (2). Establishing just positivity/normalization of p_n is insufficient. A full four-iterate invariant must propagate (4) while also controlling B_n and H_n; the source crossing theorem addresses pairs of h's, not these centered normalized gaps. I have not proved such propagation or a variation-diminishing theorem for (2).

## Exact obstruction to a single decreasing likelihood-ratio induction

This concerns the actual canonical sequence, but falsifies an auxiliary strategy, not Conjecture 1. The first normalized gap densities are

    p_1(x)=6x(1-x), p_2(x)=30x(1-sqrt(x))^2,
    p_2/p_1=5(1-sqrt(x))/(1+sqrt(x)), 0<x<1.

This ratio strictly decreases. It is tempting to induct that p_(n+1)/p_n always decreases (a usual route to ordered integral observables). It already fails for p_3/p_2.

Use h_3(x)=1-3x+2x^(3/2), k_3=3/10, d_2=1/30,d_3=1/70. From h_4'=-h_3^{-1}/k_3, one has h_4'(0)=-10/3 and h_4''(1)=-1/[k_3 h_3'(0)]=10/9; the inverse derivative at 1 is legitimate since h_3'(0)=-3. Also h_3'(0)=-3 and h_3''(1)=3/2. Since F_2=h_2-h_3=x(1-sqrt(x))^2,

    lim_(x->0+) F_3/F_2 = (h_3'(0)-h_4'(0))/F_2'(0)=1/3,
    lim_(x->1-) F_3/F_2 = (h_3''(1)-h_4''(1))/F_2''(1)=7/9.

The first limit uses first-order endpoint expansions; the second uses second-order Taylor expansions and F_2''(1)=1/2. No numerical approximation or h_4 closed formula is needed. Multiplying by d_2/d_3=7/3 gives

    lim_(x->0+) p_3/p_2=7/9 < 49/27=lim_(x->1-) p_3/p_2.

A decreasing ratio cannot have these endpoint limits. Conversely an always-increasing ratio rule is already contradicted by p_2/p_1. An alternating ratio rule is NOT disproved here, nor proved sufficient for (4), since the weight h_n+h_(n+1) also changes. This obstruction is a helper/strategy result with zero discovery credit.

## Current bounded public screen and limits

Fresh HTTP at 2026-10-29T05:54:14–16Z fetched the two actual target/companion versions, follow-up, author page, and current count-ex-machina main registry. Exact URLs, headers, hashes and timestamps are in retrievals.json. The current count registry is byte-identical to the pinned dbf673741a54c7dc9d88a6aec0e8148a538f4a3a registry reused below; this is content freshness, not a newly verified HEAD. It contains no Miyamoto/stribol/2402.06618/361811 hit.

As authorized, reused 2026-10-29T04:39:40–44Z complete-tree/head receipts in sol-fresh-analysis-discovery-r7: omega 67b4fae085cf19003a33f8027410c383b49e5046 (commit 04:37:11Z), complete D5 and Problems subtrees; count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a (2026-09-09); OpenAI math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (2026-10-26). Repeated the bounded case-insensitive path/registry screen; no target hit. This is only dated filename/registry coverage, not full-body clearance or coverage of later omega/OpenAI commits. No GitHub API traversal/retry was made. Old project pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is not treated as current novelty evidence.

Current web queries `"Miyamoto" "stribolic" conjecture proof` and `"2402.06618" conjecture proof` returned OEIS, author, original papers and a 2024 talk; no full proof located. Search results are leads, not theorem evidence. MathDB's inherited 403 at 2026-10-29T05:41:00.074762Z was respected: no retry or alternative MathDB route. GitHub rate-limit history was respected. No nomination is made; freshness/coverage would need rechecking before one.

## Runnable validation and strongest objection

Run `python check.py` from this lane. It enforces 512MiB address-space, 30s CPU, BLAS/OMP=1 before arithmetic. It independently checks the scalar recurrence expansion, four exact rational evaluations of (1) for f=h_1,g=h_2 using x=t^2, the integrated p_1 identity, and the two exact endpoint constants. These tests validate algebra; the ordinary arguments above justify the identities universally. No finite polynomial-iterate expansion/grid was pursued. No diagnostic failure or limit escalation occurred in this lane.

Strongest objection: (1)–(3) are elementary re-expressions of the nonlinear dynamics; they do not establish the new sign control demanded by (4). The centered kernel is signed, pairwise domination does not currently extend to the normalized-gap cone, and even the simplest uniform likelihood-ratio direction fails on the exact source sequence. Signed spectral explanations still lack all-index mode/projection signs and quantitative remainder control. There is no complete ordinary source proof/refutation, no PROOF.md, no Lean endpoint and no credit.

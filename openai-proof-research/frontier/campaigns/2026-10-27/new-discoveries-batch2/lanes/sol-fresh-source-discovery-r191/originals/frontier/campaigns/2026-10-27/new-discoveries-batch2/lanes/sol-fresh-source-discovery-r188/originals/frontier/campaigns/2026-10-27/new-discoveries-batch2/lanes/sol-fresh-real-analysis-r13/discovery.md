# Fresh real-analysis investigation — credit 0

Research date: 2026-10-29 UTC (local workspace date 2026-10-28). No acceptance recommendation. Counts remain 3/30 additional and 33/60 total.

## Selected full target

Roland Miyamoto, *Polynomial parametrisation of the canonical iterates to the solution of −γg′=g⁻¹*, arXiv:2402.06618v2, Conjecture 1. The actual latest body, its Theorem 1 and proof, and Proposition 2 and proof were read. The live abstract lists v1 2024-02-09 18:51:11 UTC and v2 2024-04-18 13:01:45 UTC. The v2 source is https://arxiv.org/html/2402.06618v2 . This is MathDB361811; an earlier campaign only downloaded its snapshot as a lead, without an investigation/result (parent-next-means/SCREENING.md). No substantive earlier lane for this family was located in the bounded campaign text screen.

For decreasing functions f:[0,1]→[0,1] with f(0)=1, let f*(y)=sup f⁻¹[y,1]. Set

    (Tf)(x) = (integral_x^1 f*(y)dy)/(integral_0^1 f),
    h_0=1, h_n=T^n h_0, k_n=integral_0^1 h_n,
    d_n=k_n-k_(n+1), theta_n=d_n/d_(n-1) (n≥1).

The literal full source conjecture is

    for EVERY integer m≥1:
    theta_(2m) < theta_(2m+2) < theta_(2m+3) < theta_(2m+1).

Full proof/refutation remains unresolved here. A proof just of convergence, uniqueness, fixed small m, or a generic acceleration formula is not this claim and gets no credit.

## Closest actual theorem bodies and public proof screen

The later same-author paper https://arxiv.org/html/2404.11455v2 , *Solution to the iterative differential equation −γg′=g⁻¹*, was read at Theorem 3.4 and its domination-preservation proof, Proposition 3.5, Theorem 4.1 and proof (canonical convergence), Theorem 4.9 and proof (no nontrivial periodic orbit), Theorem 4.11 and proof (global convergence), Proposition 4.12 and its Hammock-Lemma proof (a lower estimate for k). None of these read bodies supplies the above ordering of successive difference quotients. The paper contains no “Conjecture” occurrence; that is only a text observation, not a proof of non-subsumption. Its geometric domination is stronger than ordinary pointwise order. Its final lower bound is explicitly weaker than the conjecture-dependent acceleration. Do not credit rediscovery of its convergence results.

Current bounded public searches for “2402.06618 proof conjecture”, “Miyamoto stribolic convergence conjecture”, and “stribolic quotients” returned the primary papers, author listing, OEIS and a 2024 conference abstract, without a full quotient-ordering proof located. These are finite search results, not novelty clearance. MathDB HTTP returned 403 at 2026-10-29T05:41:00Z; this route was stopped, no alternate MathDB endpoint or challenge evasion attempted.

As explicitly authorized, reused complete registry trees/head receipts fetched in sol-fresh-analysis-discovery-r7 on 2026-10-29T04:39:40–44Z. Coverage: omega HEAD 67b4fae085cf19003a33f8027410c383b49e5046 (commit 04:37:11Z), complete D5 and Problems subtrees; count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a (2026-09-09); OpenAI math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (2026-10-26). Case-insensitive path/registry searches for miyamoto, stribol, 2402.06618,361811 found no hit. This is dated filename/registry coverage ONLY, not a full-body absence proof and not coverage of subsequent commits. GitHub API was not traversed or retried. Source receipts/hashes are in provenance.json.

## Ordinary analytic attempt and precise remaining bridge

Fubini applied to the subgraph of an invertible decreasing f gives

    integral_0^1 y f*(y)dy = (1/2) integral_0^1 f(t)^2 dt,
    integral_0^1 Tf = integral f²/(2 integral f).

Indeed the left integral is integral_0^1 integral_0^{f(t)} y dy dt. All integrands are nonnegative and bounded. Thus with S_n=integral h_n²,

    d_n = (2 k_n²-S_n)/(2 k_n).

This identity is elementary and uncredited. Positivity of these deficits is already implicit in the source strict descent. The sought order is equivalent to the following three sign requirements (denominators d_j>0):

    A_(2m)>0, A_(2m+1)<0, C_(2m+2)>0,
    A_n = d_(n+2)d_(n-1)-d_n d_(n+1),
    C_n = d_(n+1)d_(n-1)-d_n².

Inserting the S_n identity does not give any known sign: it couples L1 and L2 data from FOUR successive normalized inverse-integral iterates. No sign-preserving induction for these expressions has been established. This is the specific all-order gap. Source geometric domination alone has not been shown to control these four-iterate determinants.

The polynomial parametrization gives a way to falsify the FULL conjecture exactly at a finite index:

    q_0=X, q_1=1-X;
    Q_n=integral_0^X q_n' q_(n-1),
    k_n=(-1)^n Q_n(1),
    q_(n+1)=((n+1) mod 2)-Q_n/k_n.

These identities are source Theorem 1(b), with its proof through the chain rule and h_(n+1)'(h_n(x))=-x/k_n. They are not a new theorem. An exact failure of any one of A_(2m)>0, A_(2m+1)<0, C_(2m+2)>0 would be a genuine falsifier. The bounded checker reconstructs k_0,…,k_10 and verifies only m=1,2,3, all already within the source's larger calculations. No numerical approximation is used for these checks; no finite check is offered as an all-order proof.

## Exact obstruction to an ordinary-order induction

A tempting shortcut is that T preserves or reverses pointwise order on normalized decreasing convex functions. BOTH global assertions are false. Take

    g(t)=(1-t)²,
    f(t)=(1-t)²(1-t²)=1-2t+2t³-t⁴.

On [0,1], 0≤f≤g≤1, with endpoints (1,0). Also f'=-2(1-t)²(1+2t)≤0, f''=12t(1-t)≥0, and g is decreasing convex. Their areas are 3/10 and 1/3 respectively. For any t, put x=f(t). Layer-cake integration gives exactly

    (Tf)(f(t)) = [integral_0^t f(s)ds - t f(t)]/(3/10),
    (Tg)(x) = 1-3x+2x^(3/2).

At t=3/5, x=64/625 and Tf(x)-Tg(x)=16/15625>0.
At t=4/5, x=9/625 and Tf(x)-Tg(x)=-52/46875<0.
The square roots of these x are rational, so these are exact rational evaluations. The checker verifies them independently. This defeats a generic pointwise-order proof even in the decreasing convex class; it does NOT contradict the source's stronger geometric domination or its canonical conjecture.

A second shortcut is a positive moment representation d_n=integral_[0,1] t^n dμ(t). Cauchy–Schwarz would force d_1²≤d_0d_2, equivalently theta_1≤theta_2. But source exact initial k's give theta_1=1/3 and theta_2=1/5. Hence that representation for all n≥0 is impossible. This does not exclude a signed spectral expansion, a negative spectral component, a shifted positive representation, or a nonlinear invariant; none was proved sufficient here.

Strongest objection to further investment: the elementary moment reduction is not close to a four-iterate determinant invariant; abstract convergence and domination cannot simply be upgraded to ratio ordering. An asymptotic or spectral argument would still need quantitative remainders, signs of projections, exclusion of additional modes, and every finite initial index. No such estimates have been proved here. No Lean work was started.

## Preliminary lead excluded: an immediate printed-theorem consequence

Ambrus–Gárgyán, *Estimates on the decay of the Laplace–Pólya integral*, published 2025-08-05, DOI 10.1112/blms.70157. Actual author-repository published PDF, pp16–18, definitions (4.5)–(4.10), Theorem 4.2, Propositions 4.3/4.4 and their proofs were read. Source: https://publicatio.bibl.u-szeged.hu/37409/1/LaplacePolya_PUBLISHED.pdf . The unnumbered p18 conjecture is log-convexity of (f(2p))_(p≥2), where f(m)=M_m/m!, M_m=max Eulerian number, f(2p)=(2p+1)/(2p+2) J_(2p+2)(0).

Let r_p=f(2p)/f(2p-2). The already printed sharper bounds following (4.11), derived from its Theorem4.2 (Lesieur–Nicolas1992), are

    L_p=2p²/(2p²+p-1) < r_p < U_p=p(2p+1)²/[2(p+1)²(2p-1)].

For p≥4,

    r_(p+1)/r_p > L_(p+1)/U_p
      = 1 + (2p³-5p²-10p-4)/[p(2p+1)³(p+2)] > 1.

Putting p=q+4 transforms the numerator into 2q³+19q²+46q+4>0. The only remaining central index for the stated sequence is p=3, whose exact ratio f(8)f(4)/f(6)² is 2577135/2553712>1, obtained from the source finite formula (1.4). Thus the full conjecture follows by a short printed-theorem consequence and one finite calculation. It is excluded as ROUTINE, credit0; this is not a discovery nomination, and not a claim someone previously wrote out this exact bridge. Original1992 proof body was not retrieved (one guessed author URL404), but the exact relevant theorem statement is printed in the actual 2025 primary body. Registry paths searched Ambrus/Gargyan/Polya/2412.12835 and found only unrelated spectral-Polya paths. No registry badge was used for novelty.

Failure preservation: check-v1-failed.py incorrectly required p=2, outside the source sequence's interior. It correctly failed (f(6)f(2)/f(4)²=604/605<1). check-v2-failed.py fixed the indexing but contained an incorrect hand-expanded cubic and failed its rational identity assertion. Both files are preserved; check.py corrects the cubic and passes. The actual cubic is the one displayed above. A one-shot SymPy expansion used during correction omitted the requested resource wrapper; this was a process error, no resource limits were raised. The final runnable diagnostic enforces all limits before any nontrivial arithmetic. The failed BeautifulSoup import is also retained in progress.md; standard-library HTML parsing was used instead.

# Focused historical and classical-route review of r90

**Decision: recommend substantive EXCLUSION as a routine Cox-cycle construction, with historical priority still UNRESOLVED. Ordinary mathematics/source PASS is preserved. No Lean or paper investment recommended; credit 0. This is a reviewer recommendation, not root acceptance or a shared-ledger disposition.**

The decisive new evidence is the complete elementary bridge below, not the size of r90's finite exponential certificate. It produces a strictly positive-rate finite irreducible MMPP violating the same universal survival order from the standard Cox/Palm formulas. I do not claim to have found a previously printed finite-MMPP crossing. The inaccessible Liu–Neuts body remains a material historical gap. Those two judgments must not be conflated.

Solo work, no children. Scope: assigned lane only. All 55 files in root-mmpp-survival-review-freeze-r1/review-freeze.json were verified before copying; final verification covers originals and own byte copies. The ancestor/batch instructions, current ledger, NEXT, prior-campaign context, complete r90 PROOF.md, and preliminary review/provenance were read. Counts remain 8 additional / 38 total. No git, candidate/shared edits, browser tabs, accounts, contacts, posting, uploads, Lean or manuscript work. Every executed Python helper used the improved packet helper_guard.py, AS and sampled process-group RSS 512 MiB, CPU210 s, wall230 s, nominal40 ms, BLAS1; no cap increase.

## Scope retained from the ordinary review

Published target: Asanjarani–Nazarathy, ANZIAM64 (2022),54–68, DOI [10.1017/S1446181122000013](https://doi.org/10.1017/S1446181122000013), Conjecture3.9. For every finite irreducible MMPP, with C=Q-D, diagonal arrival matrix D, background stationary row pi and Palm row alpha=pi D/(pi D1), the proposed order is

    pi exp(tC)1 >= alpha exp(tC)1  for every t>=0.

r90 uses the positive-rate directed 12-cycle and D=diag(9,8,7,6,5,4,3,4,5,6,7,8)/60. Its proof gives a gap <-1/25000 at t=48/5, with pi_i=1/12 and alpha_i=a_i/72. This review does not rerun witness search or downgrade the earlier independently checked certificate. I read the full analytic argument and checked its law conventions against the prior review. The earlier math/source PASS remains supported; this focused lane does not claim a second independent numerical replay. The actual cached He2021 Section4.3 still lists stochastic order as future research, separately from his proved mean/SCV statements. Neither SCV>=1 nor the source's nonmonotone event-hazard example establishes this crossing.

## Historical bodies and chronology

**Thesis, body-level reading (under 200 words).** The author's public [Academia thesis page](https://www.academia.edu/60250963/Control_and_inference_of_structured_Markov_models) exposed the relevant complete proof text, not just an indexed summary: printed pp67–70, Propositions3.3.2/3.3.3. Proposition3.3.2 asserts SCV>=1 equivalent to stochastic order, but its proof improperly reverses integration of a pointwise inequality. Proposition3.3.3 additionally assigns the sign partition of pi-alpha to its product with a nonnegative resolvent, without a preservation theorem. The assumptions are general stationary point processes and then general finite MMPPs; no reversibility restriction rescues the order assertion. Footnote2 points to1802.08400 for updates. The title page says2017; repository metadata records publication2018-07-19 and deposit2018-09-14, DOI10.14264/uql.2018.600. Thus title-page year is not a proved public-priority date. This is a failed positive-order proof, not an earlier crossing. The repository PDF/record returned403. No thesis PDF bytes were obtained; the body reading is the public text rendering retrieved before the later direct-HTTP403, with formula-layout limitations. It does not certify all thesis pages or exact PDF identity.

**Withdrawn preprint, actual PDF acquired.** [arXiv1802.08400v1](https://arxiv.org/pdf/1802.08400v1), dated23 February2018, has Theorem3.1 on pp3–4 claiming the full MMPP order. Its first contradiction assumption is failure for *all* t, whereas negating the theorem only gives failure at *some* t. Failure even at t=0 is impossible because both survivals equal1. The subsequent integral comparison could at most settle a mean inequality; positive area does not prohibit a negative interval. The proof also treats a sign partition as preserved by right multiplication by (-C)^-1. Nonnegative entries preserve nonnegative vectors, not the location of signs in signed vectors. For illustration, (1,-1) times the positive matrix with rows(1,10),(2,1) is(-1,9), reversing both signs. This elementary objection is not an asserted MMPP resolvent example. The v1 displayed subsequent equations also lose minus signs on the negative block. None of these steps is a valid proof of the order.

The cached actual arXiv withdrawal page dates v2 to5 May2019 and v3 to19 May2019 and attributes withdrawal to a problem in Theorem3.1. The v2 PDF is absent404; I did not retry it. The replacement1905.01736v1 has Conjecture4.2, later published as3.9 in2022. The thesis and withdrawn v1 cannot be treated as established positive theorems merely because they predate that conjecture. He2021 independently proves SCV facts, not this order. No inference about an unpublished author explanation is made.

**Liu/Dan–Neuts1991, actual body NOT obtained.** DOI10.1080/15326349108807202, Stochastic Models7(3),499–509. Public Crossref/OpenAlex metadata, an Internet Archive exact-title catalogue search, and distinct author/repository-focused searches located no lawful body. OpenAlex lists only the closed publisher location, no repository full text; archive exact-title search has zero results. CORE search returned429 and was stopped. The prior review's publisher403 was not repeated. No proxy, challenge workaround, credentials or contact was used. Metadata about two-state MAP counterexamples and an MMPP2/MSPP2 equivalence is a lead only. No historical clearance follows from it. In particular MAP does not mean diagonal-D MMPP, and matching count moments does not give Palm/time waiting-time laws. Bibliographic displays disagree between1991 and a1992 online date; neither establishes body content.

## Actual classical bodies read

1. Last–Penrose, *Lectures on the Poisson Process*, author-hosted2017 PDF, [Theorem13.8, pp131–132](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf). Its joint Mecke identity for a Cox process and its directing measure implies that the environment under reduced Palm sampling is intensity-biased. Conditional Poisson void probability gives the survival functional. The proof was read. Proposition13.6 is a variance identity; it is not used as an order theorem.
2. Baccelli–Błaszczyszyn, *Stochastic Geometry and Wireless Networks I*,2009 [public academic copy](https://www.wias-berlin.de/people/koenig/www/FnT1.pdf), Theorem1.4.3 reduced Campbell formula, Section1.7.1 Cox definition, and Theorem4.2.1/inverse formula and periodic-pattern discussion. These justify the Palm/time distinctions and random-shift stationarity; they do not print the sinusoidal crossing below.
3. Asmussen–Koole,1993 [author-hosted complete body](https://www.math.vu.nl/~koole/publications/1993jap/art.pdf), Theorem1, stationary Corollary2 and its proof, and Section3. Their density theorem concerns general marked Markovian arrival streams, whose D need not be diagonal. Section3 explicitly disproves replacing that approximation class by MMPPs for arbitrary stationary point processes. Consequently I do **not** apply this density theorem to a periodic lattice process, and do not claim it supplies the Cox-specific bridge. The bridge is instead proved explicitly next.

The Cox/Palm ordering paper read in the preliminary review compares different processes in directionally convex order; its Palm caveat does not itself refute the target. No cookbook body was recovered, so no unexamined cookbook theorem is cited. The2026 Asanjarani–Hautphenne–Nazarathy article DOI10.1016/j.peva.2026.102562 surfaced as a fresh lead; its public abstract concerns moment matching, but direct body access returned403. That body remains unread, not cleared by its abstract.

## Complete classical Cox-cycle bridge to the literal finite-MMPP claim

This is my explicit reviewer derivation from the standard formulas just identified. It is **not** attributed as a previously printed theorem or crossing. It closes the substantive objection without assuming an unspecified approximation theorem, without invoking MAP=MMPP, and without a finite-exponential parameter search.

Let U be uniform on[0,2pi), and conditionally generate a Poisson process on the whole real line with intensity

    f(U+s),  f(x)=mu+epsilon cos(x),  0<epsilon<mu.

This process is stationary: time shifts just rotate uniform U. It is locally finite and simple, and its intensity is mu. Put A(U,t)=integral_0^t f(U+s)ds. Conditional Poisson void probability and the joint Cox Mecke/Palm identity give

    S_time(t)=E exp(-A(U,t)),
    S_Palm(t)=E[f(U) exp(-A(U,t))]/mu.

For completeness the Palm weighting is direct: apply the joint Mecke identity to an arrival at x, with a test of the shifted environment and no arrivals in(x,x+t]. The added atom at x is outside that open future interval. Translation stationarity makes the expected left side mu times the Palm survival per unit length. The right side is E[f(U)exp(-A(U,t))]. There is no pre/post-state ambiguity.

Write V=U+t/2 and a=2epsilon sin(t/2). Then A=mu t+a cos V. Define J(a)=E[cos V sinh(a cos V)]. Symmetry V->V+pi gives E[cos V exp(-a cos V)]=-J(a); the sine term integrates to0. Therefore the exact survival gap is

    G(t)=S_time(t)-S_Palm(t)
        =(epsilon/mu) exp(-mu t) cos(t/2) J(a).

For a>0, x sinh(ax)>=a x^2, so J(a)>=a/2>0. At t=3pi/2, take mu=1, epsilon=1/2. Here a=sqrt(2)/2 and cos(t/2)=-sqrt(2)/2. Hence

    G(3pi/2) <= -exp(-3pi/2)/8 < -1/1944.

The last strict bound uses3pi/2<5 and e<3, hence exp(3pi/2)<243. This is survival crossing for one stationary Cox process, not a hazard monotonicity statement or SCV inference.

Now transfer the strict sign to **finite** MMPPs. Let N>=3, h=2pi/N, j=floor(U/h), and let Y(s) be an independent Poisson process with rate1/h. On states0,...,N-1 use the directed-cycle generator with forward rate1/h and diagonal -1/h, and arrival rates f(jh). Its phase at s is(j+Y(s)) mod N. The initial j is uniform, and this is the unique stationary distribution. The generator is irreducible and all arrival rates lie in[1/2,3/2]. Since the sum of cos(jh) is0, the mean arrival intensity is exactly1 and the Palm weights are f(jh)/N. Thus these are literally the finite source laws.

Couple its unwrapped phase theta_N(s)=hj+hY(s) with U+s. The floor discrepancy is<h, E[hY(s)]=s and Var[hY(s)]=hs; by Cauchy–Schwarz

    E|theta_N(s)-(U+s)| <= h+sqrt(hs).

Since f is epsilon-Lipschitz, its integrated intensity A_N satisfies

    E|A_N-A| <= epsilon F(h,t),
    F(h,t)=ht+(2/3)sqrt(h)t^(3/2).

The exponential x->exp(-x) is1-Lipschitz on nonnegative x. Thus the time survival error is at most epsilon F. For Palm survival use the *normalized weights*, rather than silently transferring the time law:

    |E[f(hj)exp(-A_N)]/mu - E[f(U)exp(-A)]/mu|
      <= epsilon h/mu + (mu+epsilon)epsilon F/mu.

Consequently

    |G_N(t)-G(t)| <= epsilon h/mu + epsilon(2+epsilon/mu)F(h,t).

This tends to0; all terms and both initial laws are controlled. To make finiteness completely concrete, choose N=10^12. Then h<7/10^12, t<5, sqrt(5h)<6/10^6 and

    F < 5(7/10^12)+(10/3)(6/10^6),
    |G_N-G| < 100000189/4000000000000 < 1/3888.

Therefore G_N(3pi/2)<-1/3888<0. The rational comparison is independently checked in audit.py/audit.json, without constructing an enormous matrix or raising caps. This is an explicit admissible finite MMPP, with no limiting object left as the counterexample and no probability/source-law bridge left as a premise. No claim of dimension efficiency, rational rates or minimality is necessary for negating the source's universal claim.

**Eligibility judgment.** The missing pieces of the classical objection were a same-process survival crossing, stationarity, diagonal D, finite irreducibility, normalization of Palm laws, and preservation of the strict sign. All are now supplied. The construction uses elementary conditioning/Mecke, a trigonometric integral with a one-line sign bound, and the elementary Poisson-clock coupling. I judge this a routine complete classical route to refuting the universal statement under the campaign's exclusion standard. r90's useful small rational12-state witness is an efficient explicit realization, but the full existential refutation already follows by this routine bridge; parameter efficiency and finite-exponential certification receive no separate discovery credit. This recommendation is not based on a printed duplicate, an open label, the withdrawal alone, or an assertion that the1991 paper resolves the problem. Root should inspect the explicit bridge before adopting the recommendation.

## Current public registries and bounded limits

At2026-10-29 19:14 UTC, current default Omega HEAD is d2b0ee6e958cf646530d3476088494e349570b46, commit19:07:49 UTC. The reviewer2130bf544f7858fc3c142bb9623b7ba9464e22ba anchor is19:01:29 UTC. The new comparison has2 commits/1 added file. I fetched the complete added body at immutable HEAD and read its assumptions/statements: it treats terminal archives of two-state spatial Markov arms, seed-preserving reconstruction and Bayesian experiments, not the continuous-time MMPP/Palm survival law. Its use of event/survival terminology is not a same-object subsumer.

OpenAI remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The root-edge-irregulator-final-freeze-r1 complete baseline inventories were read and hashed: Omega350197 entries at1b999d9f..., OpenAI174524 entries. The preliminary review's chronological delta chain through r90's0292f337... and then2130bf... (11 commits/4 files, actual bodies inspected there) is preserved in own context copies. The new targeted baseline path screen found no MMPP/Markov-modulated/Cox-Palm/arrival-process paths; it is not a semantic proof of absence across all statements. Blueprint and Lean trees are not equated. This is bounded current coverage, not worldwide priority certification; no refresh of an old main branch substitutes for default HEAD.

## Exact residuals and handback

* Historical priority: HOLD. Liu–Neuts1991 actual body remains unavailable; no earlier published finite-MMPP crossing has been established by this review. The2026 moment-paper body and cookbook also remain unread. Further acquisition must use genuinely distinct lawful sources, with no repeated blocked publisher or CORE requests.
* Thesis: relevant public proof text now read and reconciled with withdrawn v1. Exact original PDF identity/layout and full-thesis duplicate search remain limited. Its claimed positive order is not accepted as a theorem.
* Substantive eligibility: recommend FAIL for the full source-refutation family, on the complete explicit classical bridge above. This is separable from historical novelty HOLD and requires root disposition, not a shared-file change by this reviewer.
* Literal Lean, paper, packet and strict extracted replay: absent and not authorized here. Do not infer formal clearance from the ordinary bridge or from r90's exact arithmetic.

Final input verification and evidence hashes accompany this report. No count or acceptance changed.

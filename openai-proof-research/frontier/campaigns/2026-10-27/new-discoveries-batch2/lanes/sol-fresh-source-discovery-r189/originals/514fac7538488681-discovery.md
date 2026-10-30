# Powered-binomial full-source continuation: unresolved

29 October 2026 UTC. No complete proof or refutation. Credit 0; no acceptance authority. Campaign counts remain 3/30 additional, 33/60 total. No Lean investment.

## Literal target and exclusion of known cases

Byun–Poznanović, *Unimodality and log-concavity of generalized Glasby–Paseman sequences*, arXiv:2604.14639v1, submitted 16 April 2026, equation (1.4) and Conjecture 1.1(a): for every positive integer m,l and every real a>0,

    S_r = N_r/D_r,  0<=r<=m,
    N_r = sum(i=0..r) (C(m,i)a^i)^l,
    D_r = sum(i=0..r) (C(r,i)a^i)^l

is weakly increasing up to some index, then weakly decreasing. Endpoints are included; ties allowed. The denominator is the full powered row. This lane freshly retrieved the actual HTML and abstract/history on 2026-10-29 at 06:31 UTC and read the literal conjecture, Theorem 1.2, its part-(a) proof, and surrounding discussion. It is still version 1. Known l=1 and l=2 cases are uncredited.

The current dated public-registry coverage is the explicitly authorized complete head/tree snapshot in sol-fresh-analysis-discovery-r7, retrieved 2026-10-29 04:39 UTC, not a new head traversal in this lane. Its omega Problems/D5 matches concern the maximum/localization. The immutable matching dossier and actual BinomialPoweredRatioMaximum.lean body were freshly downloaded here: the endpoint `maximum_asymptotic` is clause (d), assumes no unimodality, and does not settle clause (a). Count-ex-machina registry/tree and OpenAI preprints/CONTENTS were re-screened from those dated receipts. Absence of a title match is not novelty clearance.

The closest actual successor is Alex Chengyu Li, *Peaks and Gaussian Limits for Powered Binomial-Sum Ratios*, September 2026, Zenodo record 22542574, concept DOI 10.5281/zenodo.22542573. Current metadata is byte-identical to the earlier retrieval. Its cached actual PDF/text, SHA256 recorded in provenance, were read: Theorem 1.1 settles the maximum asymptotic; Theorem 5.1 and its proof settle l=2 for all positive a by partial-sum log-concavity and a nonnegative moment representation of D_r. Neither is this lane's target. The work expressly separates finite-size general-power shape.

Abel–Gawronski–Neuschel, *Binomial Polynomials* (2013), actual author-repository PDF freshly fetched, supplies Lemma 2.2 (negative real zeros of complete binomial-power polynomials) and Theorem 3.1 (fixed-power asymptotics off the negative axis). These actual statements and their proof openings were read. They concern the complete-row polynomial, not the truncated-row ratio. No bridge from their real-rootedness to the all-row inequality below was proved. This is a bounded source screen, not worldwide priority clearance. Old MathDB 403 and recent GitHub API rate limits were respected: neither route was retried.

## Independently rederived sufficient implication chain

Let u_i=(C(m,i)a^i)^l. For 0<=r<m put

    Q_r=N_r/u_(r+1),
    A_r=(r+1)^l(D_(r+1)/D_r-1),
    W_r=Q_r/(r+1)^l,  H_r=A_r W_r.

All denominators are positive. Pascal gives D_(r+1)>D_r: existing coefficients weakly increase and the new last term is strictly positive. Thus A_r>0. Direct subtraction gives

    S_(r+1)-S_r = u_(r+1)/D_(r+1) * (1-H_r).

With Q_(-1)=0 and rho_r=((r+1)/(a(m-r)))^l,

    Q_r=rho_r(1+Q_(r-1)).

For m>=2, rho strictly increases. Q_0>0=Q_(-1), and comparison of the two positive factors proves Q_r>Q_(r-1) inductively. Also

    W_r=a^(-l)(m-r)^(-l)(1+Q_(r-1))

strictly increases over 0<=r<m. If A were nondecreasing, H would strictly increase, so the signs of S_(r+1)-S_r could only pass from positive to negative, with possibly one zero. A finite sequence whose adjacent signs have this property is unimodal: choose the first nonpositive difference as the turning point, or the endpoint if none. The m=1 sequence is (1,1). This proves the **conditional reduction**, not A monotonicity.

Clearing the positive denominator D_r D_(r+1) gives exactly

    D_r D_(r+1)(A_(r+1)-A_r)
      = E_(r,l)(a)
      = (r+2)^l D_r D_(r+2)
        - ((r+2)^l-(r+1)^l) D_r D_(r+1)
        - (r+1)^l D_(r+1)^2.

This uses the corrected signs in root-powered-binomial-adoption-r1, not the erroneous display in the older r15 handoff. For l=1, D_r=(1+a)^r and E=a(1+a)^(2r+1)>0.

For integer l set x=a^l; D_r=sum C(r,i)^l x^i. Using C(n,i)=0 outside its range, define four lists, all indexed by i=0,...,r+2:

    P1_i=(r+2) C(r,i) C(r+2,j-i),
    P2_i=(r+1) C(r,i) C(r+1,j-i),
    N1_i=(r+2) C(r,i) C(r+1,j-i),
    N2_i=(r+1) C(r+1,i) C(r+1,j-i).

Write P=P1 union P2 and N=N1 union N2, retaining multiplicity and zero padding. Expansion of the three products shows

    [x^j]E = sum P_i^l - sum N_i^l,  0<=j<=2r+2.

The proposed sufficient assertion is that for every r>=0,j in this range,k, the sum of the k largest entries of P squared is at least the corresponding sum for N squared. This assertion remains UNPROVED.

Here is the precise classical bridge if that assertion were proved. For any nonnegative list z,

    sum_i (z_i-t)_+ = max_k (top_k(z)-kt).

Consequently prefix dominance gives dominance of these sums for every t>=0. If p>1, integrate against p(p-1)t^(p-2)dt; the identity

    z^p=p(p-1) integral(0..infinity) (z-t)_+ t^(p-2)dt

follows by elementary integration on [0,z]. It yields sum(P_i^2)^p>=sum(N_i^2)^p. For p=1 the total-prefix inequality suffices. Taking p=l/2 proves every coefficient nonnegative for l>=2. Nonnegative coefficients imply E>=0 at every x>0, then A monotonicity, then the full source theorem by the preceding argument. Every link after the squared-prefix assertion is justified; that assertion is not supplied by the convexity argument.

## Exact obstructions to local proofs of the criterion

Unsquared majorization already fails at r=4,j=2 (root's top-two totals 244<245); it cannot justify the needed convex-power comparison.

A new attempted local strengthening also fails even with strictly positive interior entries. At r=2,j=4,i=2, which is its own reflected partner j-i,

    (P1_i,P2_i)=(24,9), (N1_i,N2_i)=(12,27).

The squared sum difference is 24^2+9^2-12^2-27^2=-216. Hence pairing i with j-i and proving each pair dominates separately cannot work. At this coefficient the full lists are P=(32,24,9,6,4,0,...) and N=(27,12,9,9,8,0,...); their sorted squared prefixes still dominate. This is a failure of the local pairing, not a falsifier of the full criterion or the source.

Sorting each of the four component lists first and pairing equal component ranks fails too. At r=2,j=1 the nonzero lists are

    P1=(16,8), P2=(9,6), N1=(12,8), N2=(9,9).

The second-rank two-entry blocks have P=(8,6), N=(8,9), squared deficit -45; their maximal entries also fail (8<9). The combined lists nevertheless satisfy squared prefix dominance. Cross-rank compensation is essential. The first exploratory scripts also preserve simpler zero-endpoint failures; the strictly positive examples above rule out dismissing the issue as zero padding.

## Consecutive-interval formulation and remaining gap

For B_i=C(u,i)C(v,j-i), its positive support is consecutive. On consecutive positive entries,

    B_(i+1)/B_i = (u-i)(j-i)/((i+1)(v-j+i+1)).

Both numerator factors decrease and both denominator factors increase, so this ratio decreases. Thus B, B squared, and their positive scalar multiples are log-concave and unimodal. An elementary exchange argument implies that the largest-k sum of any one such block is attained on a consecutive interval: if a selected set has a gap between selected endpoints, an interior value is at least the smaller endpoint, so replace that endpoint by the gap and iterate. If k exceeds the positive support size, append zeros. Therefore if

    T_B(k)=max_s sum(i=s..s+k-1) B_i^2

with zero padding and T_B(0)=0, then for two component blocks U,V,

    top_k(U squared union V squared)
      = max_h (T_U(h)+T_V(k-h)),

where 0<=h<=length(U) and 0<=k-h<=length(V). This is exact: any selected k entries allocate h to U and k-h to V, and both individual optima are attainable.

Thus the missing assertion can equivalently be written as the comparison of the two allocation/interval maxima for (P1,P2) versus (N1,N2), uniformly in r,j,k. Log-concavity locates each individual optimum but does not compare the two pairs of optima. The exact local obstructions show why a same-index or same-rank comparison cannot simply fill that gap. No uniform interval-transfer inequality was found. The interval reformulation is an uncredited elementary helper, not the requested theorem.

## Exact diagnostics and their limits

`check.py` independently checks 364 corrected cleared-difference/expansion identities (5460 coefficient evaluations), 4485 source sign/Q/W identities, 9256 single-block interval identities and 8866 allocation identities, and the two positive-entry obstructions. Repeated coefficient evaluations at different rational weights are counted as evaluations, not distinct coefficient triples. It also checks l=1's exact E identity.

`explore.py` tests squared prefixes for all 61<=r<=150 and every j, plus selected j at r=200,300,500,800,1000: 19,388 cases pass. `sparse.py` tests 808 more cases at r=1000,10000,1000000,10^12 and coefficients within distance 100 of either degree endpoint, omitting only common zero padding. These large rows do not turn finite evidence into a uniform result. No squared-criterion falsifier or source counterexample was obtained. `blocks.py` preserves the initial rank-pairing failure. None of these diagnostics proves the source theorem.

Each diagnostic process sets RLIMIT_AS=536870912 bytes, a 20/30/45-second hard CPU deadline, and OPENBLAS/OMP/MKL threads to 1 before its computation. No limit was raised. All arithmetic is exact integers/Fractions. No diagnostic resource failure occurred in this lane. Runnable commands from this directory:

    python check.py
    python explore.py
    python sparse.py
    python blocks.py

Strongest objection: the substantive mathematical step is still missing. An all-r,j,k squared-prefix inequality, an all-r,l,a direct E>=0 proof, or the weaker full source single-crossing assertion must be established; none follows from finite diagnostics or component log-concavity. Even proving this sufficient criterion would require the complete source bridge above, and any eventual discovery claim would still need bounded novelty qualification and independent review. No PROOF.md is supplied because no full proof survived to that stage. No child, git, shared/other-lane edit, browser tab, public post/upload/contact/account action was performed.

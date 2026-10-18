# Circular reconstruction: invariant algebra, cyclic gaps, and the missing centered step

Myeongjin Kang, 2026-10-17. No affiliation asserted. Original prose CC BY 4.0; original code MIT. Third-party bodies are private provenance inputs, not publication payloads.

**Status: unresolved discovery checkpoint. No target freeze, contribution nomination, acceptance, or count.** The intended problem remains arbitrary binary circular words of known length, known fixed rational retention probability, success at least 2/3 up to rotation, with both quasipolynomial samples and a uniform decoder with a worst-stream bit-operation bound. No sparsity, aperiodicity, unique marker, special length factorization, or marked input root is imposed. Nothing below proves that full theorem. The parent reported 12/20 accepted contributions during this investigation; this item adds zero. Uploads remain stopped.

Theorems of the pinned OpenAI source at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. This note checks a prospective deduction and its unproved interfaces; it does not audit source truth. The preliminary r11 screen, obstruction, checkpoint, receipts, code and result were read completely and copied under `private/prior-r11/`. Hash verification is recorded separately.

## 1. Completing the elementary channel conversion

Write p for retention and q=1-p. Let C_x be deletion followed by a uniform cyclic root of the surviving output. Let Q_x choose a uniform input root, force that bit to survive, and delete the other n−1 bits independently. Let P_x choose a uniform input rotation and then run ordinary deletion on all n bits. These are different laws; r11's example remains valid.

The r11 identity is Q_x(t)=|t| C_x(t)/(np) for nonempty t. Consequently:

1. Accept a circular trace t with probability |t|/n, discarding empty traces.
2. On an accepted trace independently delete its first bit with probability q.

The acceptance probability is p. The conditional accepted trace has law Q_x. Step 2 restores an independent Bernoulli(p) survival decision for its formerly forced input root; the other input coordinates already have independent Bernoulli(p) decisions. Its output therefore has **exactly P_x**, including its empty output probability. Independent executions yield independent P_x samples.

Conversely, randomly rotating the surviving output of P_x gives C_x. The input rotation becomes immaterial once the output is uniformly rerooted. Data processing and the common acceptance probability give, for all length-n x,y,

    p TV(P_x,P_y) ≤ TV(C_x,C_y) ≤ TV(P_x,P_y).

For the first inequality, append the acceptance/rejection flag to C; rejection may be mapped to one symbol. Its accepted sublaw is pQ, so p TV(Q_x,Q_y)≤TV(C_x,C_y), and Q→P contracts TV. Thus the ordinary uniform-orbit mixture is a valid substitute after explicit preprocessing, at constant sample overhead for fixed p. It is not a pure ordinary trace source.

The idealized rejection description has an unbounded stopping time and must not be confused with the target's worst-random-bit running time. A finite implementation is straightforward: to request M converted samples with failure allowance δ=2^(−a), examine at most N=ceil((2M+8a)/p) circular traces and fail if fewer than M accept. Ideal acceptance indicators are independent Bernoulli(p), so the failure probability is at most exp(−Np/8)≤δ. Replace each of the at most 2N Bernoulli decisions by its downward dyadic approximation with b=ceil(log2(2N/δ)) bits. A coupling changes the complete computation with probability at most 2N·2^(−b)≤δ. All decisions and loops now have fixed finite bounds, and bit work is polynomial in N,n,the binary length of p,and b. This supplies an approximate finite simulation with total extra failure at most 2δ; it does not supply the missing reconstruction algorithm.

This conversion is elementary technical support, not a contribution nominee. Also, the r11 citation to BVW circular Definition 4 should be **Definition 5**: Definition 4 defines cyclic statistics. The correction is recorded here without editing r11.

## 2. What Fourier characters really repair

Let R_r x have coordinates (R_r x)_j=x_(j+r mod n), let ζ=exp(2πi/n), and let μ_x be uniform rotation of x (equivalently uniform on its distinct orbit). For an equivariant polynomial F of character k,

    F(R_r x)=ζ^(−kr) F(x).

Hence |F| is constant on the orbit, but for F,G of characters k,l,

    E_{μ_x}[F conjugate(G)]
       = F(x) conjugate(G(x)) · 1_{k=l mod n}.

On each fixed-character subspace the baseline Gram form has rank at most one. Different nonzero character weights are orthogonal. Thus normalizing character polynomials by their values at x does not make the adjacent cross-character inner products close to 1, as required by the source's `lem:gram-chain`. In particular it cannot give a source chain from the invariant vector 1 to a nontrivial character.

The obstruction can be seen inside one actual uniform orbit, without arbitrary mixtures. Take x=(1,0,...,0) and A_k(X)=Σ_j w_j ζ^(kj) X_j with all w_j>0. The orbit Gram matrix of A_0,...,A_(n−1) is

    H_(k,l)=(1/n) Σ_j w_j² ζ^((k−l)j).

The discrete Fourier matrix diagonalizes H; its eigenvalues are w_j². Thus det H=∏_j w_j²>0, and the rank is n. For the source-shaped Gaussian w_j=exp(−j²/(2σ²)), det H=exp(−Σ_j j²/σ²). Gaussian-windowed sums do not become a common rank-one family merely because unwindowed Fourier characters have constant modulus. This example refutes that proposed implication, not circular reconstruction or a quantitative orbit-specific scale lemma.

Magnitude data alone also lose orbit information: the two subsets {0,1,4,6} and {0,1,3,7} of Z/12Z are not translates but have equal autocorrelation. Their corresponding binary strings therefore have identical |F_k|² at every discrete frequency. The exact check is included. This is a standard type of homometric phenomenon, not a novelty claim.

There is a genuine algebraic rescue. Let R denote the Reynolds projection RP=(1/n)Σ_r P∘R_r. If F and G are invariant, then

    E_{μ_x}[F conjugate(G)]=F(x) conjugate(G(x)).

The entire invariant subalgebra, not just an individual character block, therefore has a rank-one baseline. A positive functional E restricted to invariant polynomials remains positive; normalized invariant vectors could satisfy the *algebraic* hypotheses of the source Gram argument if the needed discrepancy and normalization estimates were available.

But projection does not commute with multiplication. Exactly,

    (RA)(RB)=(1/n) Σ_h R[A·(B∘R_h)].

The sum over h is an independent relative root, which the original common-root latest-endpoint calculation does not contain. For order-one A(t)=Σ_j a_j(t)X_j, RA(t) is simply (Σ_j a_j(t))(Σ_j X_j)/n, so that first attempt keeps density and discards arrangement. Higher-order invariants are necessary.

## 3. Exact cyclic-gap algebra closure is affordable

Here is a feature class in which the relative-root sum can be absorbed without an exponential-in-n number of categories. It resolves the elementary algebraic closure question, but not the centered analytic scale step.

For k≥1 and a list z=(z_1,...,z_k), define

    G_(k,z)(X)=n^(−k) Σ_(r∈Z/nZ) Σ_(0=s_1<s_2<...<s_k<n)
                  (∏_(a=1)^k X_(r+s_a)) (∏_(a=1)^k z_a^(g_a)),

where g_a=s_(a+1)−s_a for a<k and g_k=n−s_k. The closing gap is part of the definition. For k=1 its only directed edge traverses the whole circle and has length n. If k>n the sum is zero. G is invariant, has Boolean degree at most k, and |G(x)|≤1 whenever all |z_a|≤1.

Consider m factors of orders k_1,...,k_m and put K=Σ k_r. Label all their selected positions. Use the first factor's distinguished root as the root of the merged tuple. Classify assignments by their weak cyclic ordering, including all ties; within each old tuple the labels occur in its prescribed cyclic order. There are at most K^K such categories, by assigning a rank from {1,...,K} to each label. In a category τ let v be the number of distinct selected positions. The original directed cyclic edges cover each new gap exactly once per factor. Put

    z_a^τ = ∏_(r=1)^m z_(r,h(r,a)),

where h(r,a) is the unique edge of old factor r that crosses new gap a. This statement includes an old k_r=1 self-edge, which crosses the whole circle. Expanding the product and applying X_j^b=X_j gives the exact identity

    ∏_(r=1)^m G_(k_r,z^(r))
       = Σ_τ n^(v(τ)−K) G_(v(τ),z^τ).

Proof: once the weak order and distinct merged tuple are fixed, every old label has exactly one assigned input position. Every old edge length is the sum of the new positive gaps that it crosses, so the new parameters reproduce the old weight. The product uses normalization n^(−K), whereas the merged feature uses n^(−v). These are the displayed scalar factors. Summing all categories counts each old assignment once.

Since v≤K, the coefficient absolute sum is at most K^K. Degrees grow by at most a factor m, and every new gap parameter contains one entry from each old factor. Positive dampings stay positive; conjugation preserves dampings. For m≤4 and k_r≤k, the logarithmic category cost is O(k log(2k)), exactly the kind of cost the source schedule can afford. Features with zero gap damping can still be bounded by finite n-dependent tuple counts, though that does not pay analytic continuation into the trace disks. The exact finite diagnostic checks this identity with rational parameters, ties, differing orders, and k_r=1 factors.

Thus neither an uncontrolled n-way root count nor failure of polynomial multiplication is the decisive obstruction. The source-specific **centered contour transfer** is still missing.

## 4. Three separate analytic and algorithmic obligations

**A. First disagreement and nonnegative distances.** In the source, E fixes the same initial bits as x before d and the opposite bit at d. Every polynomial using positions before d has zero discrepancy. This supplies both an initial unit signal and cancellation of every merged endpoint j<d. An invariant cyclic moment difference of integer size does not provide that prefix condition. Uniform orbit means at order one are constant in the coordinate index, so even the source's initial signal is absent when two words have the same density.

BVW circular Lemma 19 guarantees a differing cyclic moment of order at most six between different integer orbits, including binary words. That exact separation is useful, but it does not supply an ordered first discrepancy stable under all later merged features. Centering a selected *gap* at its first differing coefficient makes earlier coefficients of that particular polynomial vanish; it does not make every lower-endpoint merged feature vanish.

One possible replacement would be agreement for all configurations of cyclic width below d. Width is monotone under adding selected positions, which is promising. But the minimum covering arc of a subset need not agree with the minimum covering arc of a larger merged set: for n=10, {0,6} has minimum span 4 through the wrap, while {0,3,6} has minimum span 6 through the other side. Rewriting all old windows relative to one common cut then introduces winding constants and reversed signs. No usable cancellation-and-centering lemma is proved here.

**B. Centered contour geometry and angular control.** The source window is W(j−d), and the contour expansion orders a common set of endpoints j_1≤...≤j_m. Its telescoping identity

    Σ_r c_r(j_r−d)
       =(Σ_r c_r)(j_m−d)−Σ_(r<m)(Σ_(l≤r)c_l)(j_(r+1)−j_r)

simultaneously keeps one centered outer parameter, makes its signed frequency small, and produces positive damping links between the old tuple graphs. Prefix cancellation then bounds the tail integral without e^(s'd).

For invariant gap windows W(g_r−d), circular interleaving gives instead

    Σ_r c_r(g_r−d)=Σ_a (Σ_(r: old arc r crosses gap a)c_r) g_a−d Σ_r c_r.

The active subsets vary from gap to gap. A small total signed frequency does not ensure the active-subset sum on an appropriate new span is small. Already two complementary arcs of lengths g,n−g with signed frequencies t,−t give

    t g−t(n−g)=2tg−tn.

Their total signed frequency is zero, but the remaining gap's frequency is doubled. This does not contradict the source, whose factors have common-coordinate endpoints rather than independently rooted gap lengths.

Shifting every Gaussian contour to real part −b gives nonnegative damping on covered gaps, but also the centering scalar exp(mbd). For d=Θ(n) at intermediate b this is exponential in n, not an affordable polylogarithmic loss. Spreading that scalar uniformly across the circle subtracts mbd/n from every gap damping and may make uncovered or weakly covered gaps grow. The exact cyclic algebra above cannot remove this issue. A new contour or mask argument must control this scalar, the angular sums, and all tail contributions together. We have neither a proof of such an argument nor an orbit counterexample ruling it out.

**C. Uniform decoding, beyond pairwise orbit separation.** Even an inverse-quasipolynomial TV bound for all distinct orbits would only justify exponentially many pairwise tests. The pinned decoder avoids that enumeration by separating a true evaluation from *all* positive truncated moment functionals fixing the first wrong prefix, and by proving strict slack for a correct prefix. No corresponding circular feasibility/extraction theorem is established here. One cannot relabel a pairwise statistical test as a quasipolynomial uniform decoder.

An orbit-specific structural fact gives a possible decoder direction. If an orbit has m distinct words, a minority-branch coordinate cylinder isolates some orbit point with at most floor(log2 m) literals. Translating that cylinder isolates every orbit point with the same degree. Thus the degree-d Boolean monomial evaluation matrix V on the m orbit points, d=floor(log2 m), has a right interpolation inverse C with coefficient Frobenius norm at most sqrt(m 2^d)≤m. Explicitly C V^T=I_m. Consequently σ_min(V^T)≥1/m, and the nonzero eigenvalues of the uniform-orbit degree-d moment matrix M=V^T V/m are at least m^(−3). For m=1 use d=0. This is elementary, and all masses are 1/m even for periodic words because every distinct rotation has the same stabilizer multiplicity.

The interpolation fact indicates that exact low-order input moments have useful rank and conditioning. It does **not** show that those input moments can be recovered to the required tolerance from circular deletion samples, and it does not prove a stable finite-bit extraction algorithm from approximate trace moments. It is technical support only, not a narrowed substitute for the intended result.

There is a more direct **conditional** extraction algorithm if all invariant input monomial moments through degree D=max(6,floor(log2 n)+1) are supplied as rational estimates with error at most ε=1/(100n²). Enumerate coordinate cylinders S with at most floor(log2 n) literals. Their number is at most Σ_(j≤floor(log2 n)) binom(n,j)2^j=n^O(log n). Expand each S and S X_i into Boolean monomials. Each expansion has at most 2^floor(log2 n)≤n terms, so estimates of a=E_{μ_x}S and b_i=E_{μ_x}(S X_i) have error at most η=1/(100n). Retain cylinders with estimated a≥1/(2n), and form a candidate whose ith bit is 1 exactly when 2 estimated b_i≥estimated a.

For an isolating cylinder, a=1/m≥1/n and b_i=a times the isolated word's ith bit. The error bounds show that this cylinder is retained and every candidate bit is correct. This includes periodic words: the isolated *distinct rotation* has mass 1/m. Other cylinders may produce incorrect candidates. Verify every candidate against all supplied invariant input moments of degree at most six, accepting only discrepancies at most 2ε. A correct candidate passes. By BVW circular Lemma 19, a wrong orbit differs in some degree-at-most-six integer cyclic statistic; after normalization its moment discrepancy is at least 1/n, larger than 3ε. Hence it fails verification on the good-estimation event. Enumerating the cylinders, performing rational comparisons, and verifying all candidates takes n^O(log n) operations on numbers of polynomial bit length in the supplied estimates' encoding lengths. A fixed default output specifies failure behavior.

This pays the combinatorial extraction obligation for that *sufficient moment-estimation route*. It is not a proof that the requisite input moments are estimable. In particular S·T_I or S X_i uses latent INPUT coordinates. Multiplying a trace statistic by a guessed input cylinder does not make it an observable bounded function of a trace. The inverse-channel variance and finite-bit estimation guarantees remain wholly unpaid. The original source's positive-functional circular decoder is likewise not established.

## 4a. Concrete test of Parseval initialization without a shifted center

The parent suggested starting from integer cyclic-moment coefficients and Parseval, avoiding a first-wrong prefix or Gaussian shift. This does give a boundary signal. For

    a_d=(1/n) Σ_(j∈Z/nZ) [x_j x_(j+d)−y_j y_(j+d)],
    A(z)=Σ_(d=0)^(n−1) a_d z^d,

each coefficient lies in (1/n)Z. If A is nonzero, Parseval gives max_t |A(e^(it))|≥1/n. What does not follow is the source's interior signal and logarithmic Poisson-deficit estimate with E=polylog(n), at the initial constant scale and controlled angle.

For a concrete orbit pair let n=12m, m≥1, and take the 1-positions

    x: {0,3m,7m},       y: {0,2m,7m}.

Their cyclic gap multisets are {3m,4m,5m} and {2m,5m,5m}, so they are not rotations. The normalized two-point difference polynomial is exactly

    A(z)=(1/n)[−z^(2m)+z^(3m)+z^(4m)−z^(5m)
                    −z^(7m)+z^(8m)+z^(9m)−z^(10m)].

The coefficient at 0 cancels, every coefficient below 2m is zero, and a_(2m)=−1/n. Thus for every s>0 and every real t,

    |A(e^(−s+it))| ≤ (8/n) e^(−2ms).

At a fixed positive s this forces a signal exponent of order n, although the unit-circle signal is at least 1/n. Removing z^(2m) would restore an unattenuated constant coefficient, but this is precisely a shifted center; stability of that center under invariant products is the unpaid issue above. This example only defeats the asserted inference from a boundary signal to an affordable *constant-scale* interior signal of this degree-two feature. It is a sparse, readily distinguishable example, not a statistical lower bound, and it does not rule out other invariant features or a different scale argument.

At s≈1/n the radial loss in this example is harmless. That observation does not supply the source's angular hypothesis |ω|≤2.002s: Parseval can locate a signal at an arbitrary high frequency. Nor does it put individual gap parameters in the observable disk. For 0<p<1 and q=1−p,

    |e^(it)−q|²−p²=2q(1−cos t),

so a unit-modulus gap parameter belongs to |z−q|≤p only at z=1. In a product of invariant cyclic features the root weights cancel, but the individual cyclic gap phases generally do not. The complementary-arc calculation leaves relative phase 2t. Unwindowed product closure alone therefore does not meet the source continuation hypotheses.

The exact failed source hypotheses are now identifiable: (i) `lem:good-frequencies` requires the Poisson logarithmic-deficit bound derived from a detectable interior signal with |ω|≤2.003s, not merely one detectable boundary value; (ii) `prop:multiscale` and the continuation step require quantitative damping relative to each individual gap phase; and (iii) the contour tail bound uses cancellation for all merged negative centered distances. Parseval and invariant baseline rank one provide none of these three statements on their own. This is a source-application diagnosis, not an impossibility theorem for circular reconstruction.

## 5. Comparison with the actual source and primary operations

The pinned uniform decoder's `setup.tex`, Theorem `thm:separation`, assumes a positive order-2D moment functional fixing a first wrong prefix. `multiscale.tex`, Lemma `balanced-product`, normalizes every vector to value 1 at one word. `contour.tex` relies on common endpoints, the positive-damping connected graph and cancellation before d. `decoding.tex` estimates finite rank-moment lists and applies rational feasibility with strict slack. These are distinct ingredients; the invariant-algebra identity alone does not supply any missing geometric or decoder hypothesis.

The pinned latest-anchor companion does not remove the same issue. Its source arrays are indexed by the latest selected input position minus the first disagreement d, and every negative-offset term vanishes by prefix agreement. Its weighted phase step compares products of deterministic generating functions; the shuffle step again relies on a common latest anchor. Its theorem is sample complexity only, explicitly not efficient reconstruction. Its period-avoiding contiguous-word base and zero padding do not provide a canonical root for arbitrary circular inputs.

Narayanan–Ren's [ITCS 2021 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.18/LIPIcs.ITCS.2021.18.pdf), Lemma 13, estimates products of ordinary-root generating functions. The C→P preprocessing above puts such mixture-averaged estimators on the correct channel. Theorem 2 uses invariant values at roots of unity to certify that a rotation-averaged polynomial is nonzero, then moves to a small arc using a Littlewood bound. For fixed product order its signal and estimator bounds balance costs of order L log n and n/(p²L²), leading to the stated stretched-exponential, not quasipolynomial, sample bound. Its reconstruction proof enumerates all candidate pairs. The length restriction to a prime or product of two primes is part of that theorem. Lemma 5 recovers the contiguous O(log n)-deck; it does not reconstruct every arbitrary circular word or furnish the present target.

Burudgunte–Valiant–Wang's [circular ITCS 2026 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/LIPIcs.ITCS.2026.30/LIPIcs.ITCS.2026.30.pdf), Lemma 19, proves exact orbit separation by cyclic moments through degree six for integer sequences. Algorithm 1 and Theorem 26 operate on a constant number k of 1s, retain traces with all k ones intact, and estimate shifted gap statistics. In this note's notation that event has probability p^k; dense k=Θ(n) makes it exponentially rare. That algorithm cannot be promoted to an arbitrary-density bound by deleting its constant-k hypothesis.

The same authors' separate [July 2026 quasipolynomial preprint](https://arxiv.org/abs/2607.04073v1) is the `BVW2026` item in the pinned uniform paper's bibliography. It must not be conflated with the circular ITCS paper. Its Proposition 36 fixes the first discrepancy of two ordinary rooted strings and a window extending backwards from it. Its discussion explicitly separates quasipolynomial pairwise testing from the unresolved efficient full reconstruction in that paper. Its Theorem 43 is an ordinary sample theorem. It is not a circular full-decoder result.

The external discovery search was limited to two queries (`circular trace reconstruction quasipolynomial uniform decoder`; `"Quasipolynomial trace reconstruction" Burudgunte Valiant Wang circular`) plus the exact arXiv primary page. It is not an exhaustive worldwide novelty search. No new-to-literature claim is made. Developed-history eligibility was not certified because there is no proved candidate to nominate.

## 6. Reading and verification limits

- Complete r11 `screen.md`, `mixture-obstruction.md`, `checkpoint.json`, all three receipts, diagnostic code and result read. The mixture obstruction remains a non-orbit example; it is not reused as an orbit impossibility result.
- Pinned ordinary source: `main.tex`, `setup.tex`, `multiscale.tex`, `contour.tex`, `decoding.tex`, and `references.tex` read in full as text in this investigation. `separation.tex` lines 1–220 read here; r11's earlier reading is separately documented. `history.tex` copied but not read here. Figure TeX was read, not rendered. No full upstream proof audit is claimed.
- Pinned latest-anchor companion: `main.tex` and `summary.tex` read in full; `part-1.tex` lines 1–275 and 420–465 read, plus targeted search hits. The intervening contour/mask construction and later reference tail were not read in full. Retrieval verified each Git blob against the pinned complete preprint tree.
- NR2021 extraction: lines 1–230 and 260–800 read; remaining lower-bound and conclusion sections and deferred arXiv appendices not read. Its Lemma 13 estimator construction is deferred by the conference version and was not independently reconstructed here.
- BVW circular extraction: lines 250–420, 625–690, and 780–900 read fully here; a longer combined read had output truncation, so no additional complete read claim is made from it. Lemma 19's preceding number-theoretic dependencies were not fully read here. R11's separate earlier reading limits remain in the snapshot.
- BVW July extraction: lines 1870–1915 and 2460–2508 read; HTML introduction lines 35–91 read. No full proof verification is claimed. PDF and text hashes are recorded in `new-primary-receipts.json`.
- Exact finite diagnostics check channel conversion, the cyclic-gap product identity, orbit isolators, and a homometric pair. They are consistency checks of elementary derivations, not evidence for the missing analytic theorem, runtime bound, substantiality, or novelty.

## 7. Handoff

The useful surviving lead is the invariant cyclic-gap algebra: its multiplication cost is controlled, and its baseline really is evaluation at one orbit. The precise next task is a centered cyclic multiscale transfer that preserves an affordable signal while enforcing trace-disk damping, together with a positive-functional orbit decoder. These remain separate proof debts. Do not invoke the original multiscale proposition until every source-specific hypothesis is paid. Do not count any technical conversion, algebra identity, isolator, or method obstruction as a campaign contribution.

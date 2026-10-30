# Absolute-continuity switching and the fixed symbolic obstruction

Author proof for the exact statement in `frozen-target.md`, whose frozen SHA256 is `bab65e89a8a02cd2d5083ee5c97a293dca4b51a34be1077c3fedf4d1a880eb81`. This document makes no independent review or contribution decision. Throughout, the pinned OpenAI theorem statements and operative proofs are stipulated, including the operations internal to their proofs. The new deductions below concern their interfaces, not their truth.

## 1. Precise paid inputs

Write [S] for [OpenAI source152, pinned source directory](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/build). Each locally retained file's canonical raw URL, complete-tree Git blob, byte count and SHA256 appear in `../private/upstream/receipts.json`; a public source register lists those identities without source bodies.

We use the following stipulated inputs, with the following exact scopes.

* [S, §2, `lem:dyadic`] For a stationary square-integrable real process, the normalized maximal error of its cumulative sum from its own chord on a block of length 2^h has L2 norm c_h with sum c_h^2 finite. Translating the block by a deterministic integer does not change this bound. No independence or centering is required.
* [S, §2, `prop:good-frames`] For a compact smooth diffeomorphism preserving ANY probability mu, good derivative frame paths on [-n,n], n=2^k, have measure arbitrarily near one and diagonal chord error at most b_kn, with b_k>=2^(-k/10) and sum b_k^2 finite. The extra smooth positive density assumption is explicitly unnecessary in that section. This applies with smooth boundary. Enlarging b_k while retaining square summability preserves the chord hypotheses.
* [S, §3, `prop:finite-splitting`, `lem:bin-spaces`, `lem:relative-exterior`] The finite triangular cocycle has slow/fast splittings, uniform bin choices and relative exterior-minor stability at parameters

  B=b^(1/8), g=b^(1/2), L=ceil(b^(1/4)n), h0=exp(-Bn), r=exp(-2Bn), delta=exp(-3Bn/2).

  The hierarchy log n=o(bn), bn=o(gL), gL=o(gn), gn=o(L), L=o(Bn) is valid. These are geometric/linear operations. They do not require the smooth reference volume to be invariant.
* [S, §4, grids and `lem:switch-orbits`, `lem:switch-jacobian`, `lem:switch-injective`] On retained good input pairs in a full product cell, the two complementary switches Phi(x,y)=(z,w) remain in that cell, follow the prescribed future/past halves with error at most C exp(Cgn)r, and define an injective Borel map with countably many smooth local-diffeomorphism pieces. Its coordinate Jacobian is 1+o(1) uniformly. In particular, this last claim occurs BEFORE the proof's use of the invariant smooth density. The four individual leading factors A_x,B_x,A_y,B_y cancel in the exact determinant quotient. This entire cancellation and recovered-endpoint-label injectivity are credited to [S]. The good-set and wall requirements, rather than any density regularity, are the hypotheses used in these local constructions.
* [S, §§5–7, `prop:words`, `lem:recognition`, `lem:rates`, `prop:system`, `prop:window-entropy`, `lem:graph-windows`, `lem:cheap-scales`, `lem:graph-independent`] A fixed zero-entropy nonatomic ergodic system has the stated word families, large label-list entropy, phase recognition, symplectic graph tests, and a contradiction with the exact switching interface. Section 7 uses invariance, compact cores of measurable symbol classes, cell-conditional independence, the summable partition budget, uniform shadowing and unnormalized output domination by 2mu. It does not use smoothness of the invariant density after obtaining switching. Section 8 below details that application.

For clarity we prove the changes to the density and boundary steps, and verify that every input to the remaining operations is preserved. This is not an invocation of [S, `thm:switching`] outside its stated density hypothesis.

## 2. Cell averaging without regularity or eccentricity

Normalize the fixed smooth positive reference volume m to be a probability. Write mu=h m, where h>=0 is Borel, integrable and finite m-a.e. Replace h on an m-null set if needed. No positive lower bound is imposed.

**Lemma 1.** Let F_k be a finite disjoint collection of positive-m-measure measurable sets Q in a compact metric space, with maximum diameter tending to zero. Set U_k=union F_k, h_Q=mu(Q)/m(Q), and barh_k=h_Q on Q, zero off U_k. Then

    e_k := integral over U_k |h-barh_k| dm -> 0.

**Proof.** For continuous g put g_Q=m(Q)^(-1) integral_Q g dm. On Q,

    integral_Q |h-h_Q| <= 2 integral_Q |h-g| + integral_Q |g-g_Q|.

The last integral is at most m(Q) times the oscillation of g at diameter Q. Sum over Q. Continuous functions are dense in L1(m) on a compact smooth manifold; one proof is to approximate simple functions using inner/outer regularity and continuous cutoffs between a compact set and an open set. Thus

    e_k <= 2||h-g||_1 + omega_g(max diam Q),

where omega_g(a)->0. First fix g with arbitrarily small L1 error and then take k large. This works even if U_k changes arbitrarily, the cells are extremely oblique, or m(U_k) stays bounded away from one. No differentiation basis or nesting is invoked. ∎

Use the convention ||xi||_1=integral |d xi| for signed measures; for probabilities this is twice the usual supremum-over-sets total variation.

**Lemma 2.** On U_k x U_k let

    rho_F = sum_Q (mu|Q tensor mu|Q)/mu(Q),
    barrho = sum_Q mu(Q) (m|Q/m(Q)) tensor (m|Q/m(Q)),

omitting cells of zero mu mass in both expressions. Then ||rho_F-barrho||_1<=2e_k. Both measures have total mass mu(U_k). The first marginal of barrho is barmu=barh_k m.

**Proof.** On a cell of positive mu mass, put P=mu|Q/mu(Q) and A=m|Q/m(Q). Expanding P tensor P minus A tensor A as (P-A) tensor P plus A tensor (P-A) gives norm at most 2||P-A||_1. Multiply by mu(Q) and sum. On a zero-mu cell h=0 m-a.e., so its contribution to e_k also vanishes. ∎

These approximations charge no part of sum B_k^16. Their errors only have to tend to zero, because the retained-mass tolerance is fixed before k increases.

## 3. Boundary clearance without a density tail rate

There is nothing to prove in this section if M has no boundary. On a connected component without boundary put H=0. On a component with boundary define

    d0(x)=min(1,dist(x,partial M)), H(x)=-log d0(x)

in its interior. The boundary has m and hence mu measure zero. A smooth compact diffeomorphism and its inverse are Lipschitz, preserve the boundary, and permute components. There is a fixed A>=1 such that A^(-1)d0(x)<=d0(Sx)<=A d0(x) in the interior. Therefore Y=H composed with S minus H is bounded. It is defined arbitrarily on the invariant null boundary. The process Y(S^t x) is stationary under mu, whether or not H is integrable.

Let Z_{k+1}(x) be the source normalized chord deviation for Y on [-n,n), of length 2n. Its cumulative sums telescope to H(S^u x)-H(S^-n x). By [S, `lem:dyadic`], there are numbers c_{k+1} with sum_k c_{k+1}^2 finite and ||Z_{k+1}||_2<=c_{k+1}. Fix a small loss tolerance epsilon>0. If beta_k is the derivative sequence from `prop:good-frames`, define

    b_k = beta_k + 2 epsilon^(-1/2)c_{k+1}.

Then b_k>=n^(-1/10), sum b_k^2 finite, and Markov's inequality gives

    mu{2n Z_{k+1}>b_kn} <= epsilon.

Also, by invariance and the fact H<infinity mu-a.e.,

    mu{H(S^-n x)>n^(9/10) or H(S^n x)>n^(9/10)}
       <= 2 mu{H>n^(9/10)} -> 0.

On the complement of these two exceptional sets, interpolation of the endpoint values and the chord estimate imply

    max_{-n<=u<=n} H(S^u x) <= n^(9/10)+b_kn <= 2b_kn.

Thus every integer orbit point stays at distance at least exp(-2b_kn) from the boundary. With B_k=b_k^(1/8), we have b_k/B_k->0, and consequently

    exp(-2b_kn) / h0 = exp((B_k-2b_k)n) -> infinity.

This is more than the source's required fixed multiple of h0. All its orbit tubes, of radius bounded by C exp(Cgn)r=o(h0), remain inside M. The argument holds for every sufficiently large k. It did not sum endpoint tail probabilities, take a subsequence, or assume a logarithmic moment of the density or of boundary distance.

Intersect the derivative-good set with this boundary-good set. If compact good base sets are needed for the finite bin choices, take a compact subset losing at most epsilon by inner regularity. The frame-good compact set restricted over that subset still gives every retained base point a witness with the original diagonal estimates, now valid with the enlarged b_k. Those estimates and the asymptotic hierarchy are all that §3's geometric operations use. Compact approximations are chosen separately at each scale; no all-scales set is claimed.

## 4. Running the geometric construction with a reference volume

Fix 0<eta<1. Apply the preceding construction with tolerances small enough that the resulting good base set A_k has mu-complement less than eta/100 for all sufficiently large k. For example choose the derivative loss and each boundary loss below eta/1000, and increase k so that the endpoint tail is below eta/1000. Finitely many unused b_k terms may be any positive values.

Use the source's finite charts, coarse bins of side h0, bin-dependent reference spaces, and full product cells E_Q([0,r)^d+rj), with an extra residual cell. The source's actual bounds are ||E_Q||<=sqrt(2), ||E_Q^(-1)||<=exp(Cbn), and smooth reference volume of each cell at least a fixed multiple of exp(-Cbn)r^d. Hence the physical diameters tend uniformly to zero and

    #D_k <= exp(CB_kn).

The same count holds for the extra residual cell after increasing C. The constants here depend on the fixed smooth geometry. Enlarging b_k did not change any parameter inequality required for bin comparison, nonlinear contraction, or exterior-volume transfer.

Here is the retained-mass check, with mu rather than m as the law of inputs. Smooth chart-region boundaries have an O(h0) reference-volume neighborhood. Partial cells discard reference volume O(r/h0). Bins not meeting A_k have mu mass at most mu(M\A_k), regardless of their m mass. In each full product cell, fixed relative coordinate-wall strips of width tau r have a reference-volume fraction at most 2d tau(1+O(r)); the determinant of E_Q cancels in this fraction. Coarse-bin strips have the analogous bound O(tau)+o(1). All these statements are estimates for the fixed smooth m, whose chart density is uniformly positive and smooth, and do not assume m invariant.

Absolute continuity is uniform over measurable sets: for every a>0 there is v>0 such that m(E)<v implies mu(E)<a. For completeness choose K with integral_{h>K}h dm<a/2, then m(E)<a/(2K) suffices. Choose tau>0 small, after fixing mu and eta, so that each wall-strip family has mu mass less than eta/1000 for large k. The region and partial-cell losses tend to zero in mu. The two endpoint exclusions have these same mu masses by invariance of mu. Boundary-good points already satisfy the source's entire-orbit collar condition.

Let R_k consist of points satisfying these good, interior-wall and endpoint conditions. The finitely many losses above, with slightly smaller initial tolerances if necessary, give mu(R_k)>=1-eta/4. The original cell law rho_k has both marginals exactly mu. Hence

    G_k^0 := {(x,y): x,y in R_k and in the same full cell}
    rho_k(G_k^0) >= 1-eta/2.

Pairs containing the residual cell cannot lie in R_k. There is no conditioning or normalization after restricting to G_k^0. Null boundaries of the grids are mu-null because they are m-null.

All geometric assumptions of the paid switch construction now hold. It supplies an injective, countably locally smooth Borel Phi_k=(z_k^0,w_k^0) on G_k^0, with outputs in the same full cell, uniform shadow error tending to zero, and coordinate Jacobian 1+o(1). Since any four points x,y,z,w in the same cell have diameter O(r), the ratio of the output to input densities of the FIXED smooth reference volume m tensor m is 1+o(1), uniformly. Thus its inverse m tensor m Jacobian is at most 1+delta_k for some delta_k->0. This inference uses neither invariance nor regularity of h.

On Q x Q the flattened measure barrho has constant density mu(Q)/m(Q)^2 with respect to m tensor m. Since Phi_k stays in Q x Q, that weight is unchanged. Its smooth-branch images are disjoint by the paid global injectivity. Change of variables therefore gives

    (Phi_k)_*(barrho restricted to G_k^0) <= (1+delta_k)barrho.

Taking first marginals gives barsigma_k <= (1+delta_k)barmu_k. This is the strongest paid geometric reduction used here. Applying that inequality directly to rho_k would be unjustified for rough h; the next step addresses exactly that gap.

## 5. Excess mass and deterministic thinning

Put sigma_k=(z_k^0)_*(rho_k restricted to G_k^0). Restriction and pushforward contract the signed-measure L1 norm. Lemma 2 consequently implies

    ||sigma_k-barsigma_k||_1 <= 2e_k.

Both output laws are supported in U_k. Moreover sigma_k is absolutely continuous with respect to m: the input pair law is absolutely continuous with respect to m tensor m, and countably many local smooth diffeomorphisms, restricted to arbitrary measurable subsets, preserve absolute continuity of the pushforward. Write sigma_k=s_k m. Set c_k=1+delta_k, choosing k large enough that c_k<=5/4. Then the mass exceeding 2mu satisfies

    D_k := integral (s_k-2h)_+ dm
      <= ||sigma_k-barsigma_k||_1
           + integral_{U_k}(c_k barh_k-2h)_+ dm
      <= 2e_k+c_k e_k
      <= 13e_k/4.

For the middle estimate, c_k<=2 and h>=0 give (c_k barh_k-2h)_+<=c_k|barh_k-h|. No error is charged outside U_k because the output law is zero there. In particular D_k->0.

**Lemma 3 (exact deterministic thinning).** Let P be an absolutely continuous finite measure on M x M, with first marginal s m, where dim M>=1. For any measurable a:M->[0,1], there is a Borel set E such that the first marginal of P restricted to E is a(z)s(z)m(dz).

**Proof.** Write P=p(z,w)m(dz)m(dw), taking a Borel nonnegative density. For s(z)>0 let p_z(w)=p(z,w)/s(z). Partition M, up to an m-null set, into finitely many Borel subsets of coordinate charts with bounded coordinates. On chart region j choose an affine rescaling of its first coordinate into (0,1), and define xi(w)=j+that rescaling. Assign any value on the null remainder. Every level set of xi has m measure zero: in its chart it is contained in a coordinate hyperplane; the exceptional remainder is null. Thus every probability p_z m has an atomless xi-distribution.

Define F(z,t)=integral 1_{xi(w)<=t}p_z(w)m(dw) for s(z)>0, and zero otherwise. This is jointly Borel: the integrand is jointly Borel and nonnegative, so parameter integration is measurable. Its distribution function in t is continuous for almost every z of positive s. The probability integral transform gives that F(z,xi(w)) is uniform on [0,1] under p_z m. This transform fact follows directly from continuity of the distribution function, by its generalized inverse; flat intervals carry no xi-mass. Consequently

    E={(z,w):s(z)>0, F(z,xi(w))<=a(z)}

has conditional p_z mass a(z), including endpoints a=0 or 1. Fubini proves the asserted marginal. Null exceptions can be omitted. ∎

Apply this lemma to P=(Phi_k)_*(rho_k restricted to G_k^0), which is absolutely continuous by the same countably smooth change of variables. Define a(z)=min(1,2h(z)/s_k(z)) when s_k(z)>0, and zero otherwise. Let

    G_k=(Phi_k)^(-1)(E), z_k=z_k^0 restricted to G_k.

It is a Borel restriction of the original pair experiment. The first output density is exactly min(s_k,2h), hence (z_k)_*(rho_k|G_k)<=2mu. The discarded mass is exactly D_k. Since e_k->0, take k large enough that 13e_k/4<=eta/2. Then rho_k(G_k)>=1-eta. The partition, its weights, its cardinality, and both original input marginals are unchanged. The source uniform shadow bound persists under restriction. No additional external random seed is used: w, already furnished by the source pair switch, supplies the atomless conditional coordinate.

## 6. Completion of the auxiliary theorem

We have proved every auxiliary assertion in the frozen target for all sufficiently large k. In particular

    sum B_k^16 = sum b_k^2 < infinity,

including the boundary observable. Density approximation only delayed the threshold k0; it imposed no summability on e_k. The hierarchy gives exp(Cgn)r->0 uniformly, proving the displayed full two-sided shadow conclusion. The domination constant is exactly 2, for the unnormalized retained law. Empty slow or fast spaces are already included by the source's zeroth-exterior-power conventions; Lemma 3 needs only positive ambient dimension, not both dimensions positive.

All constants may depend on M,S,m,mu,the metric,eta. In particular the wall width and eventual approximation scale may depend arbitrarily on h. There is no effective or uniform density rate. There is no entropy or ergodicity assumption on mu. Compactness, smoothness of S and the reference m, and absolute continuity are precisely those in the frozen statement.

## 7. Fixed symbolic system and the cheap-scale interface

Fix once and for all the ergodic nonatomic zero-entropy phase system of [S, `prop:system`]. This choice precedes all model data. Suppose a model in the frozen main statement existed. In dimension zero a compact manifold is finite, so its probability cannot be measurably isomorphic to a nonatomic system. Thus dim M>=1, and the full auxiliary theorem applies with eta=.01.

The source word parameters have lengths m_i powers of two, label sizes L_i, ell_i=log_2 L_i, R_i=ell_i/m_i, and integers K_i with sum K_i R_i^16 infinite. The admissible tests have n=m_iD, where D is a power of two between 2^ceil(K_i/16) and 2^floor(K_i/8). The k-indices of these tests lie in disjoint intervals of length at least K_i/32. If B_{log_2 n}/R_i were eventually bounded below by c>0, summing B_k^16 over these intervals would contradict its summability. Therefore [S, `lem:cheap-scales`] gives tests i->infinity with

    log_2 #D_{log_2 n} = o((D-1)ell_i).

The constant converting natural logs to base2, and the model-dependent C, are fixed. This is selection inside the FINAL SYMBOLIC CONTRADICTION, exactly as in the source; it is not a repair of the all-sufficiently-large-dyadic switching theorem.

## 8. The unchanged probability contradiction

Transport the symbolic observations to an invariant conull subset of M by the proposed measurable isomorphism and extend them arbitrarily off it. The output domination ensures that the null extension does not affect retained outputs. Let C be the sampled partition cell under the ORIGINAL rho_k. Form the length q=D-1 past list U from y in [-n,0) and future list V from x in [0,n), each with its own symbolic phase alignment. Define Z on EVERY pair before restriction as the fraction of entries whose labels pass the source alternating-form graph test.

Both input marginals are mu and the conditional law given C is independent. The source `prop:window-entropy` gives entropy at least .996 q ell_i for each aligned list. Conditioning on C subtracts at most log_2 #D_k=o(q ell_i). Entropy subadditivity gives the required average conditional entry entropy at least .99 ell_i for large tests. Applying the paid independent graph estimate `lem:graph-independent` with the random entry and C gives

    E_rho Z <= .62.

For the lower bound, choose compact cores in each of the finitely many measurable symbol classes, losing total mu mass kappa, where kappa<d_*/20000 and d_*>0 is the source word-recognition distance. This is possible for ANY Borel probability on the compact manifold (and measurable classes may be replaced by Borel representatives). Distinct cores have positive mutual distance. For all sufficiently large tests the uniform switch error is smaller than this separation. Input time marginals are mu. Retained switched time marginals are at most 2mu, by output domination and invariance. The source counting/Markov argument therefore bounds the fractions of symbol errors in both halves by d_*/100 outside a set of rho mass at most .04, including the eta=.01 retention loss. Recognition `lem:recognition` then identifies the common phase and all but D/100 labels in each list. This retains the original corresponding-entry pairing used in Z; no phase of one independently sampled list is imposed on the other before switching.

The output is a legal symbolic point except on a null set, and `lem:graph-windows` fails on a set of invariant-system mass alpha_{i,D}=(2D-2)/H_i with alpha_{i,D}->0 uniformly in the admissible D. Domination by 2mu bounds its retained failure mass by 2alpha_{i,D}<=.01 for large tests. On the simultaneous good event of mass at least .96-.01, at least a fraction .96 of corresponding entries pass. Thus the identical original probability law satisfies

    E_rho Z >= (.96-.01)*.96 = .912.

These explicit constants and recognition operations are those already proved in [S, §7]; none uses density regularity beyond the now established switching interface. The inequalities .912<=E_rho Z<=.62 contradict one another. The proposed model cannot exist. The fixed system therefore excludes EVERY model in the frozen statement, including arbitrary vanishing or unbounded L1 densities and optional smooth boundary. ∎

## 9. Primary antecedents and limits of this proof

The proof's only substantive theorem inputs are the stipulated source operations and ordinary measure theory proved or explained above. Its claim is a conditional deduction from that pinned corpus, not an independent proof of its upstream assertions.

[Katok–Thouvenot, *Slow entropy type invariants and smooth realization of commuting measure-preserving transformations*, Ann. IHP Probab. Statist. 33 (1997), 323–338](https://www.numdam.org/item/AIHPB_1997__33_3_323_0.pdf), Proposition 3 and Proposition 4/Corollary 2, provides the primary covering/slow-entropy antecedent for higher-rank action obstructions. Those operations are not credited as new here. Damaged formula OCR limits the exact quantitative comparison; it is not a theorem input to this proof.

[Foreman–Weiss, *Measure preserving diffeomorphisms of the torus are unclassifiable*, arXiv:1705.04414v2](https://arxiv.org/pdf/1705.04414v2), introduction and §9, provides the equivalent-volume formulation and a realization reduction for strongly uniform circular systems with sufficiently fast coefficients. Its operation changes the symbolic construction via the circular functor and uses approximation by conjugacy; it is not a smooth normalization of an arbitrary invariant L1 density for a fixed S. The §9 body was read after freeze, explicitly recorded in the ledger. No worldwide novelty conclusion is drawn from this limited comparison.

[Goldstein–Grochulska–Hajlasz, *Constructing diffeomorphisms and homeomorphisms with prescribed derivative*, Advances in Mathematics 460 (2025), 110020](https://jyx.jyu.fi/bitstreams/b99cc98a-922b-4560-b42c-a34936a6b253/download), Theorem 1.4 and §5 Lemma 5.1/Corollary 5.3, pays L1-density cell-mass adjustment and weak differentiability normalization mechanisms. The present proof does not claim those mechanisms as new. A general such normalizer does not supply a smooth conjugate of the fixed S and does not preserve its endpoint equations. We instead keep those equations and use the source's complementary output for exact marginal thinning.

The integrated additional assertion proved here is that the density and collar replacements simultaneously preserve the original independent pair law, exact unnormalized domination, the all-dyadic square-summable geometric budget and the full model scope. Its contribution relative to these strong source operations requires independent assessment; the theorem's stronger scope alone does not establish substantiality.

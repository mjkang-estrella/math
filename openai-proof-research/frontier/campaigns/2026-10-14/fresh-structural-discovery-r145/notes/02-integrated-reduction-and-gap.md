# PREFREEZE outcome: no nominee

No full new theorem has closed. The calculations in note01 and this note are working reductions and diagnostics, not a frozen author-proof claim, not a renamed conjecture, and not a supporting substitute submitted for acceptance. The old Frankl scout/direct-information attempts remain unchanged. No source185/r144 or H138 operation is reoffered.

## Exact transfer after the strongest compatible entropy mixture

Write H for natural entropy, N=|F|, p=max_i Pr(i in X) for X uniform on a finite union-closed F with a nonempty member. Suppose the independent union Z0 and a second uniform-marginal union Zc obey the primary mixture estimate

  w0 H(Z0)+(1-w0)H(Zc) >= ((1-p)/m) log N,

with m>0 and 0<w0<=1. Jiang section3 establishes this from its two pointwise scalar inequalities; Liu's original protocol construction explains the induced conditional-IID law. Costa–Sadhu v1 Proposition6.3/Theorem1.2 uses the same compatible integration with a different scalar profile. The coupling spaces and native conditional probabilities must be retained: a symmetric pair law need not be conditionally IID, while a whole-vector global coupling need not preserve native transition laws given both prefixes.

For ANY further uniform-marginal coupling whose union entropy exceeds H(Z0) by Delta, support in F and the displayed inequality give exactly

  p >= 1-m + m w0 Delta/log N.                                  (T)

This is the operation already used by Jiang Proposition10.3. It can use the full projection gain, an affine perturbation, a product construction, or any other compatible gain; there is no requirement that this additional coupling be a coordinate protocol. Thus the independent component may be replaced after the coordinate proof is finished. A failed factorized construction does not make this replacement unavailable.

For the inverse-multiplicity projection, the already established reduction is

  Delta >= D(P0||P*) >= 0,

and the explicit affine comparison proves Delta>=V/(16 log N), with V the double-centered cost variance. Note01 gives the more general inverse-temperature identity and exact product composition. Neither identity nor tensorization is an unpaid operation.

The missing sufficient estimate can be stated precisely, without promoting it to a conjecture or frozen scope: choose a threshold p_* with 1-m<p_*<1/2 and a constant eta>(p_*-(1-m))/(m w0); then uniformly over ALL finite ground sets and ALL union-closed families of size N>=2 with p<=p_*, obtain Delta>=eta log N for a compatible coupling. Substitution into (T) would exclude those families. This round supplies neither such eta nor a proof of that estimate. A different structural inequality could succeed without taking this form. The unsupported estimate is not itself a finding.

Even maximizing Delta over all couplings does not pay it automatically: the maximum is log N-H(Z0), attained by the diagonal, whose relative size still needs proof under the small-frequency assumption. Chains exclude a size-only extensive bound but do not satisfy the small-frequency hypothesis. The Boolean product diagnostic shows that coarse range-based perturbation estimates can lose a product-depth factor; it does not give arbitrary-family control.

## The prefix-fiber loss is real

Identify subsets of {1,2,3,4} with masks. Take F={0,7,11,13,15}, namely empty,123,124,134,1234. Any two distinct nonempty nontop members have union1234, so F is union-closed. Each sample is uniform on five members.

The iid union law, in the indicated member order, is

  (1,3,3,3,15)/25.

Force both samples to share their first-coordinate prefix, sampled at its native probability; conditional on that prefix, sample independently and uniformly within its fiber. Prefix0 has the single empty member and probability1/5. Prefix1 has four members and probability4/5. Within that fiber the three nontop union multiplicities are1 and the top multiplicity13. Therefore the new union law is

  (4,1,1,1,13)/20.

The entropy difference D is exactly

  100 D = log(4^4 12^36 60^60 / (20^20 5^15 65^65)) < 0.

The integer comparison is recorded in private/prefix-exact-certificate.json, independently of the floating discovery (~-0.147289 nats). The finite diagnostic enumerated4943 union-closed families of size>=2 on a four-point labelled ground set and fourteen proper nonzero prefix masks. This certificate is for the displayed example; no universal result or contribution is inferred from the census. The witness has p=4/5, so it is not a counterexample to any low-frequency estimate. It only blocks adding fiber gains to the global iid baseline without accounting for a baseline change.

For a prefix map pi and native law mu, let nu_ab be the suffix-union law for independent uniform samples from F_a,F_b. The globally iid union prefix law is q_g=sum_(a union b=g)mu_a mu_b and its conditional suffix law is the corresponding normalized mixture bar-nu_g. The same-prefix baseline has entropy

  H(mu)+sum_a mu_a H(nu_aa),

whereas the iid baseline is

  H(q)+sum_g q_g H(bar-nu_g).

This is the precise correction term a fiber recursion must pay. It has no automatic sign, as the example shows.

## Full block optimization is compatible, but does not eliminate the gap

For a partition into prefix fibers, an arbitrary global P has block masses w_ab and conditional pair laws P_ab. Writing Q_ab for the reference Q restricted and normalized to a block and q_ab for its block masses, the KL chain rule gives

  D(P||Q)=D(w||q)+sum_ab w_ab D(P_ab||Q_ab).

The true uniform marginal constraint is, for each A in F_a,

  sum_b w_ab P_ab^left(A)=1/N,

and similarly on the right. It does NOT force every P_ab marginal to be uniform within F_a. Imposing that extra requirement is a restricted optimization and may lose the global optimum. Allowing all those block marginals preserves feasibility and reproduces ordinary global transport; it supplies no entropy-gain lower bound until a new structural estimate controls them. Conversely, conditional couplings with the native marginals for each prefix pair are always compatible and can be used in (T), provided their actual entropy comparison is proved.

The classical forward/reverse Brascamp–Lieb mechanism is not dismissed. The actual LCCV2018 Lemma1 proof tensorizes prescribed PRODUCT marginal laws by a KL chain rule and nonnegative mutual information. Its subsequent Gaussian doubling proof explicitly chooses optimal conditional couplings with potentially different marginals. Both are compatible operations where their hypotheses hold. They neither identify arbitrary prefix fibers with a product family nor preserve equality of their conditional laws automatically. Liu's sectionI flags this equal-law issue; sectionsII–III show how shared randomness preserves the narrower conditional-IID property and pays an improvement. These stronger available constructions have been incorporated.

## Strongest scalar and pinned-source comparisons

Costa–Sadhu Theorem7.1 treats an arbitrary finite number of scalar product profiles, not just Jiang's one-profile special case. Its proof tests a point mass and a two-point distribution concentrating at1: the latter forces m w0>=1/2, and the former bounds the combined profiles by log2. It yields

  1-m <= 1/2-max_(0<x<1)[x h(x)-h(x^2)/2]/log2.

Adding more profiles under those same product-minorant hypotheses cannot exceed that ceiling. The theorem is a limitation of that reduction, not of all protocols or all global couplings. The local scalar certification and the newer advertised exact-endpoint record were not fully replayed; no latest-bound claim is made here.

Pinned family119's main:soft and main:ck keep uniform cube input. More strongly, its upgrade:joining theorem accepts an arbitrary coupled pair of scalar fields and pays a mean-dependent joining profile; its proof uses the common-budget optimizer, thinning and child pooling. Its dimension induction then uses equal cube-face weights and the specific symmetric-noise edge cost. The actual upgrade and flow bodies were read, rather than treating the theorem headline as the whole operation. The Hellinger companion's induction uses compression, a small coordinate, asymmetric section profiles, scalar averaging and a monotone root bound; its conclusion supplies the entropy implication. These are stipulated true operations at their actual interfaces. No domination connecting their edge cost to the full block log-multiplicity cost above has been proved. The earlier balanced-coding obstruction rules out one proposed transport only; it does not justify claiming all source/classical compositions impossible.

There is no author theorem freeze, correctness/contribution verdict, acceptance/count, worldwide-priority claim, current-open claim, or downstream formal/manuscript/release request. The mathematical gap is the uniform extensive gain or another adequate structural comparison, not an artifact check.

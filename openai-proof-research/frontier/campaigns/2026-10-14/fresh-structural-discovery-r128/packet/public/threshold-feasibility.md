# Containment-cost rounding: strongest compatible reductions

These are prefreeze feasibility calculations, not a candidate proof or a new contribution classification. All ground sets in this note are finite. The pinned source175 integral/fractional theorem and its operative selector/rounding proof are stipulated. Write C0=25*512^4. A cover G of F means that every H in F contains some member of G. Fractional coverage means sum_{S subset H} g(S)>=1, with 0<=g<=1, including the empty set.

## Nonuniform product probabilities are already compatible

The actual Przybyłowski–Riordan primary, *Cloning in the context of the expectation-threshold conjecture*, Electronic Journal of Combinatorics31(4), P4.74 (2024), Lemma3 and Section3, gives the cloning/random-transversal interface and explicitly discusses fractional and nonuniform versions. The complete five-page primary was read. It is not merely an exchangeability heuristic.

Here is the exact application to source175. For rational positive coordinate probabilities r_x=m_x q, replace x by m_x clones. Lift F to the increasing family of clone sets whose projection lies in F. For each original S, put coefficient g(S) on every choice of one clone for each x in S. A clone set projecting to H contains at least one such transversal for each S subset H, so coverage holds. Its uniform-q fractional cost is exactly

    sum_S g(S) product_(x in S) (m_x q) = sum_S g(S) product_(x in S) r_x.

Apply source175 at q. It supplies a clone cover of cost at most1/2 at q/C0. Choose one clone per coordinate independently and uniformly, forming a full transversal V. Restrict the clone cover to sets contained in V and project. This covers every original H: the selected transversal over H is in the lifted family. For a clone generator U using distinct coordinates, its probability of being contained in V is product 1/m_x. Its projected cost at r/C0 is product(m_x q/C0). The product of those two quantities is (q/C0)^|U|. Generators with repeated coordinates never survive. Therefore the expected projected cost is at most1/2, and some V works. No symmetric minimizer needs to be assumed.

For positive real probabilities, approximate from below by rational vectors. The same fractional g stays feasible. There are finitely many possible integral covers, so a constant subsequence and continuity give the result. If some probabilities vanish, add their singleton sets at zero cost, and apply the positive-coordinate argument to the family members avoiding them. Empty families and the excluded full family are handled directly. These are compatible operations of the source plus the primary, not an unpaid nonuniform theorem.

## Uniform rank sampling also has a direct compatible reduction

For the uniform k-subset B of an n-set, put c(S)=P(S subset B). If s=|S|<=k,

    (k/(e n))^s <= c(S)=(k)_s/(n)_s <= (k/n)^s.

For the lower bound, the average of the first s terms of the decreasing list log(k),...,log(1) is at least log(k!)/k>=log k-1; also (n)_s<=n^s. Terms s>k have cost zero. For k=0 use zero-cost nonempty generators directly.

Suppose the fractional c-cost is at most1/2. Restrict the family to its members of size at most k, then take their upward closure; retain only g(S) with |S|<=k. This retains coverage and has product cost at p=k/(e n) at most1/2. Source175 gives an integral cover at p/C0. All original members of size>k can additionally be included as free generators. If B is independently thinned with retention theta=1/(e C0), each generator has cost theta^s c(S)<=(p/C0)^s for s<=k and zero otherwise. Thus the full uniform-rank transfer is paid by the source and these scalar comparisons. It is not a proposed substitute for arbitrary weighted rank laws.

## The full weighted-rank question examined, but not frozen

For every n>=1, 0<=k<=n, positive real w_1,...,w_n, let

    P(B)=w(B)/e_k(w),  |B|=k,
    c_w(S)=w(S)e_(k-|S|)(w outside S)/e_k(w),  |S|<=k,

and c_w(S)=0 for larger S. The unfrozen question was whether one absolute C>=1 works for all these data and all increasing proper F and fractional covers g: fractional c_w-cost<=1/2 should imply an integral cover with sum_G C^(-|S|)c_w(S)<=1/2. This is thinning the same law, not changing its external field, rank, or original family. No full theorem with those quantifiers was assembled.

Conditioning independent Bernoulli variables with odds t w_i on total size k gives exactly this law for every t>0. However, dividing by the rank-event probability does not give a uniform cover-budget comparison. Borcea–Brändén–Liggett, arXiv:0707.2340v2, Corollary4.18 supplies stability under exact-rank conditioning, Theorem4.9 supplies conditional negative association, and Theorem4.19 supplies stochastic ordering of adjacent ranks. The actual proofs/statements at those interfaces were read; the proof of their Feder–Mihail input is a cited sketch, not a freshly reconstructed proof here. These results do not themselves assert cover rounding.

The failure of a marginal-product replacement is exact. For n=3,k=2,w=(M,1,1),

    c_w({2,3})=1/(2M+1),
    c_w({2})=c_w({3})=(M+1)/(2M+1).

The ratio c_w({2,3})/[c_w({2})c_w({3})]=(2M+1)/(M+1)^2 tends to zero. Thus no uniform reverse product comparison, even with a fixed factor per selected coordinate, follows from the marginals. This diagnoses only that replacement. It is not a counterexample to the full question.

## A stronger operation that DOES transfer

The discrete-convexity companion's complete elementary covering lemma was read after the first weighted-rank feasibility calculations, still before any freeze. Its weighted-degree pruning, pair sampling and residual-tuple proof transfer to the actual weighted-rank containment function. This removes a possible false claim that the local covering primitive is missing.

More generally, let c(S)=P(S subset B) for a conditionally negatively associated finite law, and kappa(S)=theta^|S| c(S), 0<theta<=1. Conditional negative association, applied after requiring I=A intersect B, gives

    kappa(A union B) kappa(I) <= kappa(A) kappa(B).

This holds also with zero costs by the containment interpretation. Fix an r-uniform edge family H with sum_(e in H) kappa(e)<=2^(h+1), where h>=64 and 1<=r<=h. Include all zero-cost edges as free generators. For kappa(I)>0 define

    d(I)=sum_(e in H, I subset e) kappa(e)/kappa(I).

The source's initial budget identity remains valid as an inequality:

    sum_(I, |I|<=r, kappa(I)>0) kappa(I)d(I)
        <= 2^r sum_(e in H) kappa(e).

Select I with d(I)>T=2^(4h), and call an edge regular if it contains no selected or zero-cost generator. For a prefix union B of positive cost, group regular e by I=e intersect B. Conditional negative association gives

    sum_(e regular) kappa(B union e)
        <= kappa(B) T sum_(i=0)^r binom(|B|,i).

If kappa(B)=0 all extensions are free. This is exactly the extension estimate used in the source. Independently sample each ordered edge pair with probability pi=2^(-8h), and add its union; add residual unions of m=2^(12h) distinct edges only if all m^2 corresponding pair indices were missed. The source's unchanged estimates give initial cost<=2^(1-2h), expected pair cost<=2^(1-2h), and expected residual cost<=2^(-m). Thus the same cover bound3*2^(-h) holds. The independence here is only that of the auxiliary pair choices, so there is no false assertion that the original coordinate law is product.

This is a compatible use of the source covering proof and classical conditional negative association. It is not the requested full fractional-cover result. The source's next step uses a product-biased orthogonal expansion and an array signed measure that factors over rows to obtain both a global weight budget and pointwise high-power certificates. The integral/fractional companion instead uses joint moments of independent positive selector variables, with a multiscale selector for non-small families. A weighted-rank replacement giving those SAME simultaneous budgets and certificates has not been constructed. Producing local covers, rank couplings, or a branchwise induction without a common original-law budget does not close this step.

Park–Vondrák arXiv:2306.12576v1 was additionally read through the complete minimal-fragment cost lemma and the setup of the final iteration. It gives the stronger nonuniform product identity q^S(1-p)^S/p^S<=L^(-|S|) with p_x=1-(1-q_x)^L. Its product factorization is explicit; adjacent-rank stochastic ordering is not a replacement for it. The attempted v2 PDF URL returned404 before the explicitly versioned v1 acquisition. No fresh proof was inferred from the failed request.

Late history checks read I02's exact transversal threshold example and I77's weighted-slice heat-bath comparison. Their constant-containment and graph-switch targets differ; neither is treated as cover-rounding proof or full-target refutation. No priority conclusion is drawn from the bounded searches.

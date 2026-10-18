# Author-side critical check of the T332 ultrapower passage

Myeongjin Kang, no affiliation. Original prose CC BY4.0. This is continuation support, not an independent campaign gate, acceptance, new nominee, or novelty claim. The full unchanged target remains the universal Hilbert-to-(Radon P1(T),W1) extension statement for every nonempty complete real tree, including nonseparable/nonproper trees. No count change.

Verdict: **no gap found in the reviewed finite-hull reconstruction and arbitrary-ultrapower retraction**. The near-maximal expected-height sequence addresses the nonseparable issue correctly. The remaining barycentric requirement is also available with constant1. Moreover, a uniform cotype2 bound for probabilities on arbitrary finite weighted-tree vertex sets passes to all Radon P1(T) with the SAME constant. Together with the correctly chosen fine ultrafilter, this makes the arbitrary-tree/global-domain passage conditional only on the still-unproved finite coupling or cotype input. This does not prove that input or the full target.

The reviewed root note is t332-parent-ultrapower/note.md, SHA256 a30f81f8f4c5017cb727264827b8c68ec01f14ad826933364710f23d18c5cc54. Its bytes were not changed. The current writer checked the proof directly, without relying on the other author-side reader's verdict. Detailed provenance/read limits are in provenance.json.

## 1. Finite hulls and the countable probabilistic construction

Fix o in a nonempty complete real tree T and write h(x)=d(o,x). A hull K of finitely many points including o is the finite union of their rooted segments. It is compact, convex and a finite metric tree, with all necessary branching points included. Its gate pi_K is 1-Lipschitz, and pi_K(x) is the last point of K on [o,x]. Consequently

    d(x,pi_K(x))=h(x)−h(pi_K(x)),
    pi_K pi_L=pi_K whenever K is contained in L.

These facts hold without local compactness, bounded branching or separability. Compactness of K ensures the last point exists; uniqueness and the contraction follow from the tripod geometry.

Suppose the laws mu^K are consistent under the gates and m=sup_K integral h dmu^K is finite. Their expected heights increase under inclusion. Choosing a hull with moment greater than m−1/j and replacing successive choices by their joint hull produces a nested sequence K_j with moments m_j increasing to m. When m=0, the same construction is harmless and every law is already delta_o.

For every l, prescribe the law of (X_1,...,X_l) as the pushforward of mu^(K_l) under all earlier gates and the identity. Consistency of the laws and composition of gates verify the exact finite-dimensional compatibility. Countable product probability extension applies to the compact metric spaces K_j. The relations pi_(K_j)X_l=X_j hold simultaneously outside one null set, because there are countably many of them. The heights H_j=h(X_j) therefore increase, and E H_j=m_j. Monotone convergence gives H_j increasing to a finite H almost surely, with E H=m. Tree geometry gives d(X_j,X_l)=H_l−H_j for l≥j, so completeness yields X_j→X.

There is no hidden measurable-selection problem here. All variables and their limits lie in S=closure(union_j K_j), which is separable and complete, hence Polish. Define X=o on the measurable exceptional null set; the pointwise limit is S-valued Borel measurable. Its law is Radon on S. Continuous inclusion S→T preserves Radon regularity: a compact subset witnessing inner regularity for the inverse image of a Borel set remains compact in T. Thus the resulting mu is a Radon Borel probability on T, has first moment m, and

    W1(mu^(K_j),mu)≤E d(X_j,X)=m−m_j.

No weak compactness of the original arbitrary family, no countable cofinal collection of all hulls, and no uniform integrability assumption on an unrelated family have been used.

## 2. Recovery of every finite hull

This is the decisive nonseparable step, and the stated argument is valid. Fix ANY finite hull K and let L_j=hull(K union K_j). The law mu^(L_j) gates to mu^(K_j). Coupling a point and its gate has transportation cost m_(L_j)−m_j. The reverse inequality follows from the 1-Lipschitz function h, so exactly

    W1(mu^(L_j),mu^(K_j))=m_(L_j)−m_j≤m−m_j.

Pushing by pi_K contracts W1 and pushes mu^(L_j) to mu^K. Therefore

    W1(mu^K,(pi_K)_*mu)
      ≤ W1(mu^(L_j),mu^(K_j))+W1(mu^(K_j),mu)
      ≤ 2(m−m_j)→0.

Here mu^(K_j) and mu^(L_j) are regarded as measures on T, which is legitimate. No inclusion K⊂K_j was asserted or needed. Equality of these laws is obtained for each fixed K individually; one does not intersect uncountably many probability-one events. This proves simultaneous validity of all deterministic marginal equalities.

## 3. Uniqueness and exact recovery of W1

Let mu,nu be Radon probabilities with integrable h. For epsilon>0 choose R>0 so that each integral of h over {h>R} is small. Choose compact C carrying all but a sufficiently small amount of each measure, small enough that R times the omitted mass is small. Finite epsilon-nets for C, together with o, generate a finite hull K. On C, d(x,pi_Kx)≤epsilon; off C it is at most h(x). Splitting the latter into heights≤R and >R proves that

    e_K(mu)+e_K(nu) is arbitrarily small,
    e_K(mu):=integral d(x,pi_Kx) dmu(x).

This also proves directly that finitely supported probabilities are W1-dense: send points in each compact net cell to its net point and all remaining points to o, using a fixed ordering to make the finite partition Borel. The same height-tail estimate controls the error.

Gate contraction yields W1(projected mu,projected nu)≤W1(mu,nu). Conversely the triangle inequality and the deterministic gate couplings give

    W1(mu,nu)≤e_K(mu)+W1(projected mu,projected nu)+e_K(nu).

Taking the supremum over all finite hulls proves equation(3) in the root note exactly. In particular the consistent marginals determine mu uniquely. All Wasserstein operations here reduce to Polish supports: any Radon metric probability has a separable full-measure support, obtained from countably many compact sets carrying mass approaching1; taking its closure in complete T gives a Polish space. Finite collections of such measures share one Polish support after taking the closure of their union. Hence usual coupling, triangle, pushforward and separation properties introduce no nonseparable measure-theoretic gap.

The Radon and finite-moment assumptions are being used, not discarded. Completeness is essential: on T=[0,1) rooted at0, assign delta_a to the hull[0,a]. The laws are consistent and their expected heights have finite supremum1, but no law on T realizes them. The missing endpoint is exactly where the Cauchy construction would fail. This is a test of the hypothesis, not a counterexample within the target.

## 4. Every bounded metric ultrapower retracts

Let U be any proper ultrafilter on a nonempty index set I. For a uniformly first-moment-bounded family (mu_i), every projected family on K lies in compact P1(K). Compactness holds because K is compact metric and W1 induces the weak topology there. Thus each U-limit mu^K exists. Continuous gate pushforwards preserve the consistency equalities, and the expectations of the continuous bounded height on K remain uniformly bounded by the original moment bound. Sections1–3 construct R[(mu_i)].

For another bounded family (nu_i), all W1(mu_i,nu_i) lie in a fixed compact real interval, so L=lim_U W1(mu_i,nu_i) exists and is finite. For each K, continuity of distance and the contraction of pi_K imply

    W1(mu^K,nu^K)=lim_U W1((pi_K)_*mu_i,(pi_K)_*nu_i)≤L.

The exact supremum formula of Section3 proves d(R[mu_i],R[nu_i])≤L. This simultaneously proves descent through the zero-ultradistance equivalence relation and 1-Lipschitzness on the metric quotient. Constant families are fixed by uniqueness. Principal ultrafilters are included; no freeness, countable incompleteness, countable index set, or countable cofinal family of hulls is required for this retraction.

The uniformly bounded representative convention is sufficient for extension. Under a convention allowing merely a finite U-limit of distance to the basepoint, change the representative to the basepoint outside a U-large set on which that distance is bounded. This produces a uniformly bounded equivalent representative. If an author's 'ultracompletion' additionally completes the metric quotient, R extends uniquely by continuity: P1(T) is complete. To see completeness without separability of T, a Cauchy sequence of Radon P1 measures lives on the closure of the union of its countably many separable supports, a complete Polish subspace; apply Wasserstein completeness there and include its Radon limit into T.

The note's two loss-of-moment examples are correct. On a ray, (1−1/n)delta_o+(1/n)delta_n has every bounded-hull projection converging to delta_o but moment1. Distinct leaf point masses on a unit star also project to delta_o along a free ultrafilter. R need not preserve the original moment or arise from a tight limit of the original family. Neither behavior contradicts contraction or its being a retraction.

## 5. Exact generalized Ball requirement and the available barycenter

The pinned source's cor:extension invokes the DUAL BANACH corollary for ell1. That corollary alone does not apply to the probability target. The applicable primary statement is Mendel–Naor, arXiv1301.3963v2, Theorem1.11: Markov type p for the source, metric Markov cotype p for the target, and Wp-barycentricity of the target with constant Gamma imply uniform finite-subset extensions. The source has M2(H)=1. Definition1.3 concerns finite probability distributions on the metric target; the stronger p-barycentric variance inequality of Definition1.4 is NOT a hypothesis of Theorem1.11. It appears in a separate sufficient route to cotype and in Corollary1.12.

For Y=P1(T), define B(sum_a alpha_a delta_(mu_a))=sum_a alpha_a mu_a. Finite mixtures preserve Radon regularity and finite first moment, and B fixes point masses on Y. Given a finite coupling beta_ab of two distributions on Y, choose approximately optimal T-couplings between each mu_a and nu_b. Their beta-weighted sum is a coupling of the mixtures. Letting the approximation errors tend to zero yields

    W1(B(alpha),B(beta))≤sum_ab beta_ab W1(mu_a,nu_b).

Infimize over finite couplings to obtain W1-barycentricity with Gamma=1. Cauchy–Schwarz on the coupling gives W2-barycentricity with the SAME map and constant1. There is no requirement to mix an arbitrary non-Radon distribution of measures, or to select optimal couplings measurably over an uncountable parameter set.

One must not upgrade this to a 2-barycentric variance inequality for the mixing map. A concrete failure occurs already on the three equally spaced points0,1,2 of a line. Identify a probability with its tail pair (a,b)=(mu{1,2},mu{2}), where0≤b≤a≤1 and W1 is the ell1 distance. Put c=(1/2,1/4), e=1/16, mu_+=c+(e,−e), mu_−=c+(−e,e), and x=c+(e,e). All are valid probabilities. Their mixture is c; d(x,c)=d(x,mu_+)=d(x,mu_−)=d(c,mu_+)=d(c,mu_−)=2e. The variance inequality would require (2e)^2+(2e)^2/K^2≤(2e)^2, impossible for finite K. This does not refute the available W2-barycentric inequality, any other possible barycenter, or T332.

Primary URL: https://arxiv.org/pdf/1301.3963v2 . The operative finite-mixture step was also checked directly in Lemma5.2; the full Section5 proof was not read or independently re-proved in this check.

## 6. Uniform finite-tree cotype passes to arbitrary T

Assume an absolute C such that Y_V=P(V), with W1 for the induced tree distance, has metric Markov cotype2 at most C for EVERY finite weighted tree vertex set V including its branching points. The edge lengths may be arbitrary positive numbers. This is an assumption for this section, not a result supplied by the retraction.

Fix n,t, a reversible stochastic matrix A and stationary probability vector pi, and input laws mu_1,...,mu_n in P1(T). Write B=(1/t)sum_(s=1)^t A^s. Remove zero-weight states first: for i with pi_i>0 and j with pi_j=0, reversibility implies a_ij=0. The positive support J is closed under A, the restricted rows remain stochastic, and its Cesaro powers agree with the corresponding entries of B. All cotype summands involving the other states have zero coefficient. It therefore suffices to construct witnesses on J; choose delta_o for any remaining indices at the end.

By finite-support density from Section3, choose mu_i^k with W1(mu_i^k,mu_i)→0 simultaneously for every i. At each k, take the hull of the union of their finite supports and o, and include its endpoints, all support points and all branching points as vertices V_k. Subdividing edges if necessary makes a finite positive-edge-length tree; repeated vertices/zero-length edges are removed. The intrinsic tree distances agree with those in T, and W1 for vertex-supported measures is unchanged because a coupling only sees the endpoint metric.

Apply the assumed finite cotype bound to obtain nu_i^k supported on V_k with

    sum_i pi_i d(mu_i^k,nu_i^k)^2
      +t sum_ij pi_i a_ij d(nu_i^k,nu_j^k)^2
    ≤ C^2 E_k,
    E_k=sum_ij pi_i B_ij d(mu_i^k,mu_j^k)^2.

Here d=W1. The finite tuple convergence makes E_k bounded and convergent to E for the original tuple. For each i in J, the displacement term gives

    d(mu_i^k,nu_i^k)≤C sqrt(E_k/pi_i).

Since the mu_i^k have uniformly bounded first moments, so do the nu_i^k, separately for each of the finitely many i. The constants may depend on this fixed positive pi_i; there is no need for a lower bound on pi_i uniform over all chains. The final cotype constant does not inherit this temporary boundedness constant.

Choose a free ultrafilter on the positive integers and set nu_i=R[(nu_i^k)]. Since [(mu_i^k)] is the constant class mu_i, contraction of R gives

    d(mu_i,nu_i)≤lim_U d(mu_i^k,nu_i^k),
    d(nu_i,nu_j)≤lim_U d(nu_i^k,nu_j^k).

Take squares, multiply by the nonnegative fixed coefficients, sum finitely many terms, and pass to the ultralimit of the displayed finite cotype inequality. Continuity of squaring on bounded intervals and of finite sums gives exactly the original cotype inequality with constant C. Reinsert zero-weight states as described. This proves N2(P1(T))≤C, with no separability, properness, support, diameter, branching or edge-ratio restriction on T.

## 7. Finite extension to a full arbitrary-domain extension

Assume the preceding cotype conclusion. Theorem1.11 and Section5 supply a constant K0 C for every finite-subset extension from a Hilbert space, with K0 universal. Fix a nonempty A and a0 in A; write y0=f(a0). Index by the finite subsets S of H that contain a0, and choose one such finite extension F_S:S→Y agreeing with f on S intersect A. Let U extend the filter generated by the cones {S:E⊂S} for finite E⊂H. These cones have the finite intersection property, so such a FINE ultrafilter exists. It may be principal in a finite setting; freeness is not itself the relevant property.

For each x in H define g_S(x)=F_S(x) when x belongs to S and g_S(x)=y0 otherwise. The anchoring at a0 gives, for every S,

    d(g_S(x),delta_o)≤d(y0,delta_o)+K0 C Lip(f) ||x−a0||.

Thus each x determines a bounded ultrapower class Phi(x). On a U-large cone both x and y lie in S, so the ultradistance of Phi(x),Phi(y) is at most K0 C Lip(f)||x−y||. On the cone containing a in A, g_S(a)=f(a), hence Phi extends the diagonal copy of f. Compose with R to get the required full-domain extension with the same bound. Empty A and zero-Lipschitz maps have constant extensions directly.

The word 'free' alone in a compressed primary ultrapower discussion cannot replace the fine-cone condition. For example a free ultrafilter on finite subsets of the integers can concentrate on subsets of the even integers and miss a specified odd point forever. This is a presentation condition for constructing the extension, not a defect in the root note's stronger retraction for every ultrafilter.

## 8. Exact conditional consequence and remaining debt

The separate parent coupling-interface note was read in full. Its conditional median construction was checked against the pinned source's actual expected-coordinatewise-median formula: multiplying each binary cut coordinate by the nonnegative atom weight times edge length commutes with median; three tree vertices have a vertex median when branch vertices are included; averaging those medians produces valid probability marginals; summing edge coordinates contracts the enlarged ell1 distances. Applying the source BEFORE averaging preserves the square of the first expected transport cost, as stated.

Consequently, IF every finite family of vertex probabilities on every finite positive-weight tree admits a single joint coupling satisfying E d(X_i,X_j)≤r W1(mu_i,mu_j) for all pairs, with universal r, the parent argument gives C^2=3024 r^2. Sections5–7 then imply the entire unchanged T332 target with a universal extension constant at most K0 sqrt(3024) r. This is a precise conditional conclusion. The simultaneous coupling hypothesis has not been proved in this check, need not be necessary, and cannot be replaced by an n-dependent constant or by a path/ultrametric restriction. No remaining compactness or barycentric debt is identified for this route; the substantive finite input remains unpaid.

No numerical diagnostic is offered as proof. No Lean formalization, full primary-paper audit, priority search or independent gate was performed. Root assistance requested the finite-to-general cotype addition; this writer supplied and checked its argument. The pinned upstream truth is stipulated, and this check does not audit it. All root notes and frozen campaign packets remain unchanged.

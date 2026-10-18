# Finite-subtree consistency and ultrapower retraction for tree probabilities

Author-side support for the unchanged T332 target. Myeongjin Kang, no affiliation; original prose CC BY 4.0. This note is not independently reviewed, not a separate nominee, and not a proof of the missing uniform finite-tree coupling or metric Markov cotype estimate. No novelty claim is made.

Let T be an arbitrary nonempty complete real tree, with fixed root o. Let P1(T) consist of Radon Borel probability measures with finite first moment, equipped with W1. Neither properness nor separability of T is assumed.

## 1. Consistent probabilities on finite hulls

Let F be the directed family of convex hulls of finite subsets of T containing o. Each K in F is a compact finite metric tree (possibly a point). Let pi_K:T→K be the nearest-point gate. Rooted tree geometry gives:

- pi_K is 1-Lipschitz;
- if K⊂L, pi_K pi_L=pi_K;
- for x∈T, pi_K(x) lies on [o,x], so d(x,pi_K x)=d(o,x)−d(o,pi_K x).

Suppose a probability mu^K on every K∈F is consistent: (pi_K)_*mu^L=mu^K whenever K⊂L. Assume

    m := sup_(K in F) integral_K d(o,x) dmu^K(x) < infinity.

Then there is a UNIQUE mu∈P1(T) with (pi_K)_*mu=mu^K for every K∈F. Its first moment is m.

Proof of existence. Choose a nested sequence K_j∈F whose first moments m_j tend to m. To do this, choose finite hulls attaining within 1/j of the supremum and successively take their union's convex hull. Consistency and the height identity imply monotonicity of the first moments under inclusion.

There exist jointly distributed X_j with law mu^(K_j) such that pi_(K_j)(X_l)=X_j for all j≤l almost surely. Indeed, the joint law of (X_1,...,X_l) is prescribed by pushing mu^(K_l) through (pi_(K_1),...,pi_(K_(l−1)),Id); these finite-dimensional distributions are consistent. The standard countable compact-space probability extension theorem supplies the joint law. There are only countably many consistency relations, so they hold simultaneously off one null set.

The random heights H_j=d(o,X_j) increase, and E H_j=m_j≤m. Monotone convergence gives H_j↑H<infinity almost surely, with E H=m. Moreover X_j∈[o,X_l] for j≤l, so

    d(X_j,X_l)=H_l−H_j.

Thus X_j is Cauchy almost surely, and completeness gives X_j→X∈T. All X_j and X lie in the separable complete closed subtree S=closure(union_j K_j). The pointwise limit X is measurable as an S-valued random variable (define it as o on the null exceptional set). Its law mu is a Borel probability on Polish S and hence Radon; inclusion into T preserves that property. Its first moment is E H=m. Furthermore

    W1(mu^(K_j),mu) <= E d(X_j,X)=m−m_j →0.        (1)

It remains to check EVERY finite hull, not just the selected countable family. Fix K∈F and let L_j be the finite hull of K∪K_j. Its mean m_(L_j)≤m. The deterministic gate coupling gives

    W1(mu^(L_j),mu^(K_j)) = m_(L_j)−m_j <= m−m_j. (2)

The upper bound follows by coupling a point and its gate; the reverse bound follows because distance from o is 1-Lipschitz. Applying pi_K, using consistency for K⊂L_j, and then (1), yields

    W1(mu^K,(pi_K)_*mu)
      <= (m−m_j)+W1(mu^(K_j),mu) →0.

Thus all required projections agree. Notice that the sequence K_j is selected by near-maximal expected height; it need not be geometrically dense in T. This is what permits nonseparable T.

Proof of uniqueness and distance recovery. For any two Radon finite-first-moment probabilities mu,nu on a complete metric tree, compact sets capture arbitrarily much probability mass, and distance from o is integrable. Taking finite nets of such compact sets and adjoining o produces finite hulls K with

    integral d(x,pi_K x) dmu(x) + integral d(x,pi_K x) dnu(x)

arbitrarily small. More explicitly, first truncate the height tails, then choose a compact set with sufficiently small remaining bounded-height mass, then a finite net; on that compact set gate distance is at most the net radius, and elsewhere it is at most d(o,x). Therefore both projected measures approach the original ones in W1. Gate contraction and the triangle inequality show

    W1(mu,nu)=sup_(K in F) W1((pi_K)_*mu,(pi_K)_*nu).       (3)

This proves uniqueness.

## 2. Retraction from an arbitrary metric ultrapower

Let U be any ultrafilter on any index set I, and consider the metric ultrapower of P1(T) based at delta_o. A representative is a family (mu_i)_(i∈I) with sup_i W1(mu_i,delta_o)<infinity; families at U-limit distance zero are identified.

For each K∈F, the family (pi_K)_*mu_i lies in compact metric P1(K). Its U-limit mu^K therefore exists in W1. The gate consistency maps are continuous, so the limits are consistent. Their first moments are bounded by the uniform bound on the representatives. Section 1 constructs a unique probability R([(mu_i)]) with these finite-hull marginals.

For two bounded representatives (mu_i),(nu_i), set L=lim_U W1(mu_i,nu_i). This exists and is finite. Continuity of distance in P1(K) and gate contraction give, for every K,

    W1(mu^K,nu^K)
      =lim_U W1((pi_K)_*mu_i,(pi_K)_*nu_i) <=L.

Equation (3) implies W1(R[(mu_i)],R[(nu_i)])≤L. In particular R is well-defined on equivalence classes and 1-Lipschitz. If mu_i=mu is constant, its finite-hull marginals are exactly those of mu, so uniqueness implies R[(mu_i)]=mu. Thus R is a 1-Lipschitz retraction from every such ultrapower onto P1(T).

This does not assert weak compactness or uniform integrability of the original family. Moment may be lost. For example, on a ray, (1−1/n)delta_o+(1/n)delta_n has moment 1 but every fixed finite-subtree projection tends to delta_o, so the retraction sends its class to delta_o. On a countable unit star, a sequence of distinct leaf point masses likewise projects to delta_o along a free ultrafilter. These behaviors are consistent with 1-Lipschitz retraction and with the earlier counterexamples to ordinary tightness arguments.

## 3. What this would settle for T332

This gives a concrete way to discharge the arbitrary-ultrafilter, nonproper-target passage once a suitable finite extension theorem has been established with a universal constant. The relevant generalized Ball theorem's other target hypotheses (including the precise barycentric requirement) must still be checked rather than assumed. The finite simultaneous-coupling hypothesis in the separate parent note is NOT proved here, and the full T332 target remains unresolved. The support lemma is not counted separately and has not undergone an independent proof/contribution gate.

## Reading and scope

The finite-tree flow and source-median setup comes from the earlier frozen analytic-r39 packet and the parent coupling note. This derivation uses standard real-tree gates, probability extension on a countable product of compact metric spaces, and Radon regularity. It does not import a new literature claim about all Wasserstein ultrapowers. No finite diagnostic or hash proves its mathematics. Critical verification of the full argument, especially the all-finite-hulls recovery and nonseparable case, remains requested.

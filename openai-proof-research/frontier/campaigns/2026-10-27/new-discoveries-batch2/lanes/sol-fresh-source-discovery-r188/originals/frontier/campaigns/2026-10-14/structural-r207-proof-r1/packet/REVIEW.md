# Structural207 independent mathematical correctness review r1

Authorized reviewer runtime: Codex / GPT-6 Astra / xhigh / default service tier. This review used no delegated workers.

**Verdict: PASS for the entire unchanged frozen statement and the submitted proof, relative to the stipulated upstream truth.** No essential repair, additional hypothesis, narrowed conclusion, changed constant, or replacement theorem is needed. This verdict includes the auxiliary mathematical claims in the proof, the three examples, and the mathematical source comparisons described below. There are no unresolved mathematical objections from this review. This is solely a correctness verdict; it assigns no contribution grade, acceptance, or count.

## 1. Exact object, independence, and premises

The reviewed author root is `frontier/campaigns/2026-10-14/fresh-structural-discovery-r207/`. The independent review root is `frontier/campaigns/2026-10-14/structural-r207-proof-r1/`. All work and copied controls of this review remain in the latter. The immutable inputs are:

| Author artifact | SHA256 |
| --- | --- |
| `packet/FROZEN.md` | `7e9597aa5af080257a8a1f88e7a99a3bc41d3c0668fcf3e109076c4097d1d4e2` |
| `packet/AUTHOR-PROOF.md` | `e12d5904e7e5bca7a31156114443ef74281b44f45def977f024e1ef10b3d25ce` |
| `packet/FINAL.md` | `3143ca3bd3708fdfda18e3d38b74bd77d5add05b55d01a62ad91888039e21c5f` |
| outside `MANIFEST.json` | `4be53433bbd39ef3805d1b6b3424db92809a4053836fc81076dee2a850e36e23` |
| outside `REPORT.md` | `e457e25176f7a4f58ada7cd504abf9b21c1cb8377fd7e92394b5d10d9355af02` |

The frozen statement and proof are copied byte-for-byte into the private submission directory of this review packet. Those copies do not replace or amend the author originals. The full FROZEN, AUTHOR-PROOF, DERIVATIONS, AUTHOR-CHECKS, READING, FINAL, and outside REPORT were read. References below to numbered equations and sections are to AUTHOR-PROOF unless another source is specified.

The exact project-root AGENTS.md, sources/upstream.json, the complete current brief and quoted original briefs, and acceptance bytes [4801,6347) were read. The acceptance slice has the required SHA256 `f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984`. The operative upstream statements and proofs at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I checked their actual domains, operations, and compatibility; I did not treat them as targets for a new correctness audit.

There were no earlier independent findings or author responses for this round. No author check, author reading claim, artifact authentication result, peer outcome, or parent assessment is used as independent mathematical evidence. The entire other-review namespace and its aliases were excluded. There was no peer contact, nested agent, broad history scan, git operation, browser UI, publication, or downstream formalization.

The prospective guard installation contains all 337 full-path wildcard/no-r patterns, all 162 substrings, and the derivative predicates. Matching uses complete project-relative POSIX paths after casefolding. Author packet access used the exact selected manifest exception, not a containing-directory exception. History section-1 was integrity-bound only and never semantically read. The two admitted mathematical history sections were read at their disclosed extents. No history or literature exhaustion is claimed.

## 2. What the PASS covers

For the real closed L1 span of the path products on the specified countably branching tree, it covers separability, completeness, infinite dimension, the exact first-Wasserstein compact-closure hypotheses, the equivalence between AMUC and essential unboundedness of every closure law, both midpoint conventions, and the displayed quantitative estimate

    Delta_X(t) >= t Theta_K(4 C_K/t)/(4 C_K) > 0,   t > 0,
    alpha_K = min_K E|W-W'| >= rho_0 > 0,
    C_K = 1 + 2 sqrt(3)/alpha_K.

It also covers the common positive interval of zero midpoint moduli when a bounded law occurs only in K, and, for every equivalent norm with a||z||_1 <= N(z) <= b||z||_1, the exact closed interval

    delta_N(t) = 0,   0 < t <= a rho_0/b.

All mixed finite lists and coefficients in Theta_K remain allowed. Multipliers may be zero and may have infinite second moments. The proof imports no reflexivity, Daugavet property, measure compactness, FDD, unconditional basis, or complex-scalar assertion.

The following objections were raised during independent examination. Each resolution identifies the existing argument that discharges it; the elaborations make that argument explicit and do not repair or change it.

## 3. Law topology, normalization, and scalar moments

**Objection 1: weak closure alone would lose the means and uniform separation, and nonconstant assigned laws would not suffice for every closure law.** The closure is in d1. An almost optimal coupling gives |EU-EV| <= E|U-V|, and weak limits retain support in the closed half-line. Every law in K consequently remains nonnegative, integrable, and mean one. The function rho(mu)=E|W-1| is 1-Lipschitz in d1. For alpha(mu)=E|W-W'|, taking an independent copy of the coupling proves 2-Lipschitz continuity. Thus rho >= rho_0 on the closure. Conditional Jensen gives alpha >= rho; compactness gives the stated minimum. In particular delta_1 is absent and every closure law is nonconstant. The upper bound alpha <= 2 follows from nonnegativity and mean one. Resolved by Section 1, under the exact topology stipulated.

**Objection 2: the Euclidean lower estimate might clandestinely use a multiplier second or fourth moment, or fail for mixed laws or zero atoms.** For a fixed finite deterministic list c, the finite fair-sign space gives ER^2=sum c_i^2 and ER^4 <= 3(sum c_i^2)^2. Hölder in exactly the displayed exponents yields E|R| >= ||c||_2/sqrt(3), including c=0. For each symmetric D_i, a fresh sign times |D_i| has the same law, including the atom at zero; independent signs and independent magnitudes reproduce the joint product law. Apply the finite deterministic sign estimate conditional on the magnitudes and then the convexity of the Euclidean norm. This yields

    kappa(a) >= ||(|a_i| E|D_i|)_i||_2/sqrt(3)
             >= alpha_K ||a||_2/sqrt(3).

No iid hypothesis is used. The reverse estimate kappa(a) <= 2 sum|a_i| and the Lipschitz bound (2) use only E|D_i| <= 2. They establish definiteness, continuity, measurability for random coefficients, and integrability whenever their finite absolute first-moment sum is finite. The Euclidean norm of a finite realized coefficient vector is finite pointwise and is bounded by its absolute coordinate sum. None of these statements requires the expectation of its square. Resolved by (1)-(2).

The normalized set defining Theta_K is nonempty: for any mu in K the single coefficient 1/alpha(mu) works. Its excess expectations are finite and between zero and one. These facts remove a possible empty-infimum or infinite-value ambiguity.

## 4. Uniform positivity of Theta_K: compactness and persistent coefficients

**Objection 3: E|S_n|=1 gives tightness but not uniform integrability, so a bounded weak limit could lose its nonzero first moment.** The proof uses more than this normalization. Under vanishing excess at a fixed r, for M>2r,

    E[|S_n| 1_{|S_n|>M}] <= 2 E(|S_n|-r)_+.

Given an error tolerance, the right side is uniformly small for all sufficiently large n; then M is increased to control the finitely many earlier integrable variables. This proves uniform integrability of the entire chosen sequence. Markov gives tightness. Weak subsequential compactness for real probability laws applies, without a Banach-space compactness hypothesis. Truncated continuous absolute-value functions and uniform integrability give E|Z|=1. Bounded continuous truncations of the excess show (|Z|-r)_+=0 almost surely. Symmetry is preserved by weak convergence. Thus (4), including all three of its assertions, is justified. For r<1 these assertions are already contradictory; treating that case by the same subsequent argument is harmless.

**Objection 4: a surviving coefficient must retain an actually unbounded law, and its remainder must be both tight and independent in the limit.** Jensen over the other centered summands gives |a_ni| alpha(mu_ni) <= 1, so every coefficient is bounded by 1/alpha_K. If maxima do not vanish, select an index in each row with absolute coefficient bounded below, absorb its sign into the symmetric difference, and extract a positive coefficient limit. Compactness of K supplies a d1 limit of those very selected laws. Independent pair couplings give d1 convergence of the differences; multiplying by the converging coefficients also converges in d1, using their uniformly bounded first moments. Integrating out the selected mean-zero summand gives E|R_n| <= 1, hence tightness of the remainders. A further weak subsequence preserves the already chosen coefficient and law limits. Product characteristic functions then identify Z with aD+R with independent factors.

**Objection 5: an independent unbounded factor might be canceled by the remainder to produce bounded support.** Choose finite A with P(W'<=A)>0. Essential unboundedness of the selected limit law gives P(D>B)>0 for every finite B. Choose finite H with P(R>=-H)>0. Independence gives positive probability of aD+R>r by choosing D>(r+H)/a. This rules out bounded support, regardless of the lower tail of R and without moment assumptions on its limit. The argument crucially uses a law in compact K, not merely unboundedness of the laws before passage to the limit. Equations (4)-(5) therefore force max_i |a_ni| -> 0. Resolved.

## 5. Infinitesimal rows, characteristic products, and bounded iid roots

**Objection 6: Bernoulli thinning need not preserve the first absolute moment, and the resulting roots might not be tight.** For any deterministic selected subset, condition on its summands and integrate the independent centered complement. Jensen bounds the expected absolute selected sum by E|S_n|=1. Averaging over independent Bernoulli selectors proves E|Y_nm| <= 1, hence tightness, for each fixed positive integer m. Each thinned law is symmetric. Only a separate weakly convergent subsequence for each fixed m is required; no common subsequence over all m is asserted or used.

**Objection 7: a logarithmic characteristic-function comparison may break down when H_n diverges, when factors initially are negative, or when a limiting characteristic function is zero.** For any fixed real t, symmetry makes phi_ni real and z_ni=1-phi_ni nonnegative. The first-moment bound gives z_ni <= 2|t|max_i|a_ni|=:eta_n -> 0. Thus eventually every factor 1-z_ni is positive. The proof only uses logarithms after this point. Bernoulli's inequality gives B_n^m >= A_n. The scalar logarithmic inequalities on 0<=z<=eta_n<1 give

    B_n^m <= exp(-H_n),
    A_n >= exp(-H_n/(1-eta_n)).

Subtracting and using 1-exp(-u)<=u and H exp(-H)<=1/e gives exactly (6):

    0 <= B_n^m-A_n <= eta_n/[e(1-eta_n)].

This bound is independent of the finite row length, m, and H_n. It remains valid if H_n diverges and requires no division by a characteristic function or its limit. When t=0 or H_n=0 the difference is zero. Initial negative factors for finitely many rows do not affect the limit. Resolved without invoking a named limit-law theorem.

**Objection 8: pointwise subsequences might depend on t, so the claimed distributional identity could fail to hold for all t at once.** For a fixed m, choose a subsequence on which the laws of Y_nm converge weakly. The S_n laws still converge to the previously chosen Z on that subsequence. Weak convergence of these laws entails convergence of their characteristic functions at every real t along that same subsequence. Apply (6) for an arbitrary fixed t; its eventual starting index may depend on t, which does not change the subsequence of laws. Hence phi_Z=phi_Ym^m as functions on the whole real line. Uniqueness of characteristic functions identifies the sum of m independent copies with Z. No diagonal extraction indexed by t is missing.

**Objection 9: the bounded-support root contradiction might use unassumed variance, or might establish only one root order.** If P(Y_m>r/m)>0, the event that all m independent copies exceed r/m has positive probability and gives a sum greater than r. Symmetry rules out the corresponding negative tail as well. Thus |Y_m|<=r/m almost surely. Only now are its mean zero and finite variance used. Since the sum has law Z,

    Var(Z)=m Var(Y_m) <= r^2/m.

This is true for every integer m, even though different m used different subsequences and different root laws. Z itself is fixed. Thus Var(Z)=0, and its symmetry forces Z=0, contradicting E|Z|=1. The entire argument permits arbitrary finite row lengths, arbitrary real coefficients, and arbitrary mixed law lists in K. It proves strict positivity for every fixed finite r>0, which is exactly the universal quantifier over r in the statement. It does not assert a positive infimum over all r or over different compact families. Resolved.

## 6. The actual product space, heads, and first exits

**Objection 10: completion or zeros might invalidate the path norms, dimension, or head projections.** The index set of edges is countable and every path is finite. Independence, nonnegativity, and mean one give EP_v=||P_v||_1=1 even with zeros or infinite second moments. Closure in real L1 gives a Banach space; rational finite combinations of countably many generators give separability. If a finite linear combination of the first-generation W_j-1 vanishes, integrating all coordinates except one gives c_j(W_j-1)=0 almost surely. Nonconstancy forces every coefficient to vanish. This proves infinite dimension without L2 orthogonality.

For finite predecessor-closed T containing the root, the coordinates after the last ancestor in T are independent of G_T and have product mean one. Therefore Q_T P_v=P_{v_T}. Conditional expectation is contractive in L1. Its range on finite combinations lies in E_T, and finite-dimensional closedness gives the same range on X; it fixes E_T, so it is a finite-rank projection. Its kernel is closed and of finite codimension. Applying I-Q_T to finite-product approximations proves density in that kernel using ||I-Q_T||<=2. The proof never asserts this complement is contractive and never invents an infinite first-exit expansion for an arbitrary completed vector. Resolved by (7) and Section 3.

**Objection 11: overlapping ancestors could destroy conditional independence, or conditioning on B could change the exit laws.** Write a finite representation y=sum_v c_v P_v. If i is a first exit and i^- its parent, its coefficient is explicitly

    B_i = P_{i^-} sum_{v extending i} c_v
                         product_{edges strictly after i, through v} W_edge,

with an empty strict-descendant product equal to one. The other terms form the old-coordinate function d. First exits are an antichain: predecessor closure prevents an exit from being a proper ancestor of another first exit. Their strict-descendant coordinate blocks are disjoint. Shared ancestors of different exits all lie in G_T. Consequently, after conditioning on G_T, the B_i are independent. No exit variable W_i occurs in any B_h, for any h. The whole B vector is thus independent of the entire exit vector conditionally on G_T. Conditioning further on the whole B vector leaves the exit variables independent with their fixed, assigned laws mu_{i^-}. The laws depend on vertices, not on random ancestor values.

Conditional expectation of y now gives d+sum_i m_i=0 with m_i=E(B_i|G_T), proving (8). If P_{i^-}=0, the corresponding B_i is zero; no ratio by P_{i^-} occurs. These facts supply the explicit overlapping-ancestor and vanishing-product handling implicit in the coefficient description. Empty exit lists produce zero tails and cause no exception.

Every coefficient is a finite sum of finite path products. Each such product has a finite first moment by independence; hence each B_i and m_i is integrable, as are d and the finite sums used below. Conditional integrability holds outside one null set for the finite list. Conditional copies B_i' can be constructed by fresh copies of the disjoint strict-descendant coordinate blocks, retaining the old coordinates. This avoids any hidden need for an abstract conditional-copy theorem. Resolved.

## 7. The first-moment comparison and affine estimate

**Objection 12: (9) might be an L2 estimate in disguise, or have an incorrect constant.** With old coordinates fixed, write y=sum B_i(W_i-1)+sum(B_i-m_i). For fixed B, independent fresh exit copies and Jensen bound the first term's expected absolute value by kappa(B). For the second term, the conditional copies just described give

    E|sum(B_i-m_i)| <= E|sum(B_i-B_i')|
                    = E E_sign|sum epsilon_i(B_i-B_i')|
                    <= E||(B_i-B_i')_i||_2
                    <= 2 E||B||_2
                    <= (2 sqrt(3)/alpha_K) E kappa(B).

The sign equality uses conditional independence and symmetry of the coordinate differences. The sign upper bound uses Cauchy--Schwarz on a finite sign space after the realized coefficients are fixed. Its subsequent expectation is finite because E||B||_2 <= sum E|B_i|. Thus no random coefficient is assigned an unproved second moment. Adding the bounds gives exactly C_K=1+2sqrt(3)/alpha_K, conditionally and then unconditionally. Measurability and integrability of kappa(B) follow from (2) and the upper bound in (1). Resolved.

**Objection 13: affine symmetrization may fail in the presence of d, or the threshold cases may lose a factor.** The real scalar identity yields M_t(x,y)=E(t|y|-|x|)_+. After fixing G_T and the entire B vector, u and d are fixed. For f(s)=(t|s|-|u|)_+, convexity and evenness give

    f((z-z')/2) <= (f(z)+f(-z'))/2.

The two exit resamplings have the same conditional law. Their subtraction cancels d, proving exactly (12). This is an even-convex comparison, not centering d by an unjustified mean-zero assertion.

Put A=|u| and k=kappa(B). When k>0 and 2A/(tk)<=r, the normalized symmetric sum has excess at this threshold at least Theta_K(r), so the right side of (12) is at least tk Theta_K(r)/2. This dominates Theta_K(r)(tk/2-A/r). When 2A/(tk)>r, the latter expression is negative, and nonnegativity supplies the required inequality. Equality at the threshold belongs to the first case. When k=0, (1) gives B=0, and the desired right side is nonpositive. A=0, zero coefficients, and empty exit lists require no division. All quantities have finite first moments. Integration, followed by (9), gives exactly (11), with no factor missing.

## 8. Completion and all modulus quantifiers

**Objection 14: a finite-tail inequality might fail after completion, or the finite-codimensional choice might depend on the direction.** Inequality (13) follows from the norm triangle inequality and gives the needed continuity in both variables. Kernel density from Section 3 transfers (11) to all completed tails. Fix t and choose r=4C_K/t, so A_t=t theta/(2C_K)=2B_t and B_t=theta/r=t theta/(4C_K)>0. At a unit center x, first choose finite u with ||x-u||<epsilon, then choose one finite predecessor-closed T containing its paths. Neither depends on y. For every y in F_T with ||y||>=1,

    M_t(x,y) >= A_t-B_t||u||-2epsilon
             >= B_t-(B_t+2)epsilon.

Take the infimum over these directions, the supremum over admissible subspaces, let epsilon decrease to zero, and only then take the infimum over unit centers. This proves the frozen lower bound at every t>0. No limiting subspace, attained supremum, or FDD is required.

**Objection 15: maximum and average conventions, or sphere versus exterior-ball directions, might differ at precisely the needed quantifiers.** At a unit x, choose a norming functional ell. Intersect any cofinite F with ker ell. Both signed endpoint norms are then at least one. On this intersection the average excess is at least half the maximum excess. Restricting to the intersection increases the maximum infimum. Taking suprema gives the centerwise factor-two comparison, and taking the infimum over x preserves it. The pointwise reverse comparison is immediate. This proves (15). For either symmetric expression, the radius function on a fixed ray is even and convex, hence nondecreasing for nonnegative radii; rescaling any direction of norm at least one to the sphere cannot increase its value. Thus both direction conventions have equal infima. Finite-codimensional subspaces of this infinite-dimensional X have nonempty unit spheres. These arguments apply also when proving zero moduli, not only positivity. Resolved.

## 9. Full L1 weak nullity

**Objection 16: testing cylinders alone proves too little, and an L2 or unconditional-basis shortcut would be invalid.** For a fixed v, the density P_v defines a probability nu=P_v dP. It depends only on finitely many ancestor coordinates. Under nu, a fresh child coordinate has its original marginal and is independent of every cylinder avoiding that coordinate. This follows directly by product integration; zeros in the density do not matter.

For arbitrary bounded measurable g, bounded finite-coordinate cylinder functions g_l approximate g in L1(nu), with |g_l|<=||g||_infinity. The countable product sigma-field, or its completion modulo null sets, has this density property. For child indices outside the finite coordinates of g_l, the cylinder pairing with W_vj-1 is zero. Splitting the remaining error at |W_vj-1|=H gives exactly (16). Its tail term is independent of j and tends to zero by integrability of the fixed parent law. Choose H, then l, then j outside the finite cylinder. This proves pairing convergence for every L-infinity function g. Probability L1 duality gives full weak nullity in L1, and Hahn--Banach transfers it to the closed subspace X. No bound uniform in v is needed here: each parent is fixed before taking its child limit. Also

    ||P_v(W_vj-1)||_1 = EP_v E|W_vj-1| = rho_v >= rho_0.

Thus the weakly null increments have the exact norms used later. Resolved.

## 10. Necessity at a bounded law only in the closure

**Objection 17: the obstruction might require a bounded law at an actual vertex, use merely approximate unit directions, or let the zero interval shrink along vertices.** A bounded mu_* in K has rho_*>=rho_0>0 and finite L_*=ess sup|W-1|>0. Metric closure supplies a sequence of assigned laws mu_vn converging in d1 to mu_*. Their normalizers rho_n converge to rho_*>0.

For each fixed v, the center P_v is positive and has norm one. The directions y_j=P_v(W_vj-1)/rho_v are exactly unit and weakly null. Positivity gives the pointwise factorization of the scalar excess by P_v, and child independence then gives the exact centerwise identity (17), even if P_v is unbounded or vanishes.

For every closed finite-codimensional F, the quotient images of y_j converge to zero in norm because they are weakly null in a finite-dimensional space. Choose z_j in F with ||z_j-y_j||->0; this is the definition of quotient distance, with an arbitrarily small additional error if the distance is not attained. Then ||z_j||->1, so eventually z_j is nonzero. The vectors z_j/||z_j|| are actual unit vectors in F and still converge in norm difference to y_j. Continuity of M_t gives the infimum upper bound for this arbitrary F. The centerwise supremum is therefore at most h_v(t), and Delta_X(t)<=h_v(t).

Choose once and for all t_*=rho_*/(2L_*). For every fixed t in (0,t_*], the limiting integrand is zero. Under almost optimal couplings, the inequality in Section 8 is valid because positive part and absolute value are 1-Lipschitz:

    |h_vn(t)-h_*(t)| <= (t/rho_n)E|U_n-U|
                     + t|1/rho_n-1/rho_*| E|U-1| -> 0.

The normalizers may vary, but they stay bounded away from zero and converge. The same t_* works for the whole limiting sequence; the conclusion is pointwise for every t in that fixed interval, as stated. Nonnegativity and (18) give Delta_X(t)=0. Equation (15) gives zero in the maximum convention as well. No uniform-in-t convergence is required. Resolved, including the case that no vertex has law mu_*.

## 11. Every equivalent norm and the endpoint

**Objection 18: the one-sided modulus might be negative, the quotient approximation might lose the endpoint radius, or the tree growth might fail to be uniform across parents.** For any N-unit x, a norming functional's kernel gives N(x+t y)>=1 for all its unit directions. Hence the centerwise supremum and delta_N(t) are nonnegative.

Suppose delta_N(t)=d>0 at a fixed 0<t<=a rho_0/b. For each unit center u, its centerwise supremum is at least d, so an admissible F can be chosen with all unit-direction gains at least 3d/4; an attained supremum is unnecessary. Convexity on each ray extends the gain to every w in F with N(w)>=t.

At any parent v, u=P_v/N(P_v), and z_j=Z_vj/N(P_v) is weakly null with N(z_j)>=a rho_v/b>=t. Approximate it in F by w_j. If N(w_j)<t, rescale it to norm t. Eventually w_j is nonzero because N(z_j)>=t>0, and the added error is

    t-N(w_j) <= N(z_j)-N(w_j) <= N(z_j-w_j).

Thus the repaired vectors still approach z_j in N. This is the decisive endpoint argument: it works when t=a rho_0/b and no strict slack is available. The proof then selects a child with N(P_child)>(1+d/2)N(P_v).

The constants a,b,d are fixed independently of v. Every path product has inherited norm one, so its N norm lies in [a,b]. Each parent has an infinite weakly null child sequence, enabling the local choice, and the tree has arbitrarily long finite paths. Repeated selection gives a(1+d/2)^m<=b for arbitrary m, impossible. This proves exactly zero, not merely nonpositivity or failure at a smaller safety radius, throughout the frozen closed interval. Equivalent norms preserve the continuous linear functionals and hence the weak-null input; no preservation of the inherited midpoint modulus is claimed. Resolved.

## 12. Examples and auxiliary assertions

The Pareto density (3/2)s^(-5/2) on [1,infinity) integrates to one, its mean is 3, and its second moment diverges. Therefore W=T/3 is positive, nonconstant, mean one, unbounded, and has infinite second moment. The singleton family satisfies every frozen hypothesis, so the stated AMUC/no-AUC example follows. The finite-variance fixed-law feasibility observation in DERIVATIONS is also covered by the stronger proved scalar lemma; it is not an additional unproved premise.

For the bounded-limit example, mu_*=(delta_(1/2)+delta_(3/2))/2 has rho_*=L_*=1/2. Coupling the mixture to mu_* gives d1(mu_n,mu_*) <= epsilon_n E|U-V| with any independent integrable U~nu, V~mu_*. This tends to zero. The sequence plus its limit is compact in d1. Every positive mixture weight of the Pareto law retains unbounded support and infinite second moment, while positivity and mean one persist. Linearity of rho gives rho(mu_n)>=(1-epsilon_n)/2>=1/3. Every depth occurs, so the specified assignment has exactly the asserted closure. The necessity argument's t_* is 1/2. Thus every assigned law can be unbounded while both midpoint moduli vanish on the stated interval. This is a single product tree, with no sum-of-spaces substitution.

For the varying Pareto/exponential mixture example, the curve is d1-continuous: coupling matching portions of two mixtures bounds their d1 distance by |s-s'| times a finite first-moment coupling cost between the endpoint laws. Its image is compact, and any assignment's closure is a compact subset. Every mixture, including both endpoints, is unbounded. Rho is affine in the law and is bounded below by the positive minimum of its endpoint values. The common bound using the whole curve is valid. If K is the actual closure and L the whole curve, then alpha_K>=alpha_L, C_K<=C_L, and Theta_K(r)>=Theta_L(r). Theta_L is nonincreasing in r. These facts compare the frozen lower bound to t Theta_L(4C_L/t)/(4C_L), independently of the assignment. Alternatively the scalar and conditional estimates already hold on the larger fixed family. The assertion in Section 10(c) therefore has the advertised uniform meaning.

The stated exclusions are respected. Nonnegative products of first-moment variables suffice throughout; no assertion extends to arbitrary signed multipliers or complex scalars. A compact family containing delta_1 is outside scope. There is no universal positive lower modulus over different families. The result does not assert reflexivity, a basis, measure precompactness, a Daugavet property, or a graph embedding theorem.

## 13. Actual source interfaces and comparison checks

The full independent read ledger, exact primary ranges, and coverage limits are in `private/READING.md` and `private/read-log.jsonl`. The 99 canonical blobs were independently authenticated against the complete pinned 13223-entry tree, not the truncated tree.json and not merely the author's authentication claim. The seven-folder selection is exactly 120 entries. Authentication is not counted as proof reading.

**Companion 6 is the operative predecessor.** Its complete conditional-products section and the introduction, exponential, Gaussian, and obstruction sections were read. Its original multiplier assumptions are identical strictly positive nonconstant mean-one laws with finite second moment. The actual head projection, first-exit decomposition, conditional coefficient estimates, midpoint identity, affine completion lemma, special-law scalar estimates, and bounded-tree argument were inspected. The submitted theorem is not obtained by silently applying that finite-variance theorem to new laws. Sections 1-9 supply the needed replacements: mixed-law kappa, uniform excess, conditional first-moment comparison, full L1 weak nullity, and the endpoint quotient repair. The old finite-head and first-exit operations remain valid by the explicit product calculations above. In particular, the distinction between conditioning on old coordinates and conditioning further on the whole coefficient vector matches the actual source construction.

**Companions 1 and 2.** The forest component/outer-Hilbert structure, the infinite coordinate closed span, the paired estimate, the stronger arbitrary-displacement lens, and the bounded-tree endpoint operation were read in their actual proofs. Finite-height Hilbert equivalences alone are not used to infer reflexivity of an arbitrary union; the source uses its precise outer sum and dual decomposition. Its infinite coordinate predual is distinguished from the whole dual. The joint-budget lens really permits arbitrary displacement and gives ||Q_H y||<=2 sqrt(R^2-||x||^2); the opposite crossing heads are nested and their simultaneous splitting pays the stated budget. The cited paired average and maximum/average conversions have the stated constants and domains. The actual endpoint-law, original-coefficient, radial, fractional matching, parent/exit sign, maximal-gain trimming, target-tail sign, and sequential comparison proofs were also read where named by DERIVATIONS. Their hypotheses remain those of their specified segment spaces, not this product X.

**Companion 3.** The actual normalized countably branching diamond metric, all-pairs distortion convention, separated midpoint selection, and iteration in the metrics proof give D^2>=1+k/4 for the forest and infinite coordinate models. This is the stronger comparison, rather than the earlier 1+k/12 bound. The introduction and recursive applications were additionally read to distinguish the norms, root conventions, and power-loss transfers. No graph upper embedding or converse lacking its reflexivity/unconditional hypotheses is imported into the submission.

**Companion 4.** The construction and exact-modulus proofs were read. The clipping argument uses measure-precompactness of the whole unit ball, not just a generator set, and the diametral finite-codimensional construction uses the Daugavet property. These yield the cited exact averaged and one-sided curves max(t/2,t-1) and max(0,t-2) in that source's setting. The completed whole-ball enlargement and its heavy-tail estimates were inspected. Neither required hypothesis is silently assigned to the present X; the author makes no claim to improve those exact formulas.

**Companion 5.** The constrained models, complete linear path-cost argument, complete quadratic path-cost argument, and segment-start/incomparable-segment proofs were read. The distinct quotient norms and their completions were retained. The source supplies the named fresh-layer 400, predictable 495, variation 252, adaptive absolute-constant, and leakage 1024 estimates, the quadratic tail constants 8, 7, and 9, segment-start denominator 64, and incomparable-segment radial constant sqrt(2)+sqrt(6). The proofs use their specific head, support, timing, and sign assumptions. None is repackaged as a product-space premise.

**Companion 7.** The full foundations, energy, obstruction, stopping, and variable-exponent sections were read. Free joining root, fixed-zero root, and outer-sum norms remain distinct. The stopping propagation, logarithmic lens, and variable-exponent cubic and sixth-power estimates are actual source operations with the specified completions and bounded-tree inputs. They do not provide an unstated structural hypothesis for the product X.

This comparison checks the mathematical descriptions and compatibility assertions. It is not a contribution verdict, a certification of worldwide priority, or an independent reproduction of every alternative proof in every companion. Unused alternative sections and manuscript PDFs not separately semantically read are identified in the read record rather than represented as read. Every source operation on which the frozen proof depends was read in its actual body; the submission’s probabilistic argument was assessed directly, not accepted on its classical attribution.

The actual primary bodies selected by the admitted packet were also read: DKRRZ Sections 1-2 and 5, Baudier's complete three-page note, Kadets-Werner Sections 1-2, the countably branching diamond proof in Section 4 of arXiv:1612.01984v1, Bartlett-Mendelson's symmetrization proof, Levina-Vershynin's Gaussian decoupling proof, and Johnson-Schechtman's binary-diamond construction in Section 3. DKRRZ's unconditional-basis renorming result has that hypothesis; its weak-null characterization has its stated additional restriction. The proof here does not invoke either without it. The Gaussian decoupling limitation is not treated as a theorem for arbitrary multipliers; the submitted elementary even-convex symmetrization is proved afresh. Finite-branching diamond constructions are not substituted for countably branching selections.

The Andrews-Mallows publisher access failure is disclosed in the author record; I did not acquire or read that primary proof. Its special-law mixture operation is explicitly proved in the stipulated canonical companion, which was read. No conclusion here depends on substituting a snippet for that inaccessible proof. The history D88 section was used only at its disclosed mathematical extent for the finite/countable diamond distinction; the adjacent compatibility section's MAP paragraph follows from the contractive finite heads and density, with uniform convergence on compact sets by a finite-net argument. The administrative history section-1 supplied no premise. Other-family material encountered inside an admitted complete section was not developed or used.

## 14. Formal and artifact evidence limits; final disposition

The actual comparator endpoints were inspected. IndependentProducts has four target `sorry` bodies; DaugavetModuli has three; ForestSpace, MidpointLenses, DiamondDistortion, BoundedTreePotentials, and RecursivePotentials have one target `sorry` each. Their imports are Mathlib only. The eight indicated navigation/comparator files were also independently retrieved at the exact pin and matched byte-for-byte to the admitted copies, as recorded privately. Local foundational declarations or proofs and the navigation document do not establish those endpoints, and none establishes the present compact-law theorem. No formal endpoint coverage is credited, no Lean compilation was used as a mathematical gate, and no new formalization was performed.

The admitted author's read-only verifier was inspected before running it with all three explicit detached anchors. It verified the exact 146-file/39-directory selection and modes. Its SHA256 is `358f4b2d0fc6d8decb3ad88d166befd14e2c5903e8dd5996fa58a7afee5e66c0`. The review uses an inspected copy of that general verifier with its own fresh manifest; the author's manifest is never used as the seal of this reduced review selection. Proportionate controls used a complete copy of the two-file author control baseline and its manifest/report, solely inside this review root. The baseline passed; byte, file-mode, directory-mode, extra-file, missing-file, and wrong-anchor perturbations were rejected. No original author file or mode was changed. These tests concern artifacts only.

**Final mathematical disposition: PASS, unchanged full scope.** Each substantive objection raised above is resolved by the submitted reasoning and its stated premises. There is no outstanding frozen assertion, auxiliary proof step, example, or mathematically operative comparison requiring repair. The source/primary reading limits and absent formal endpoint support are disclosed limitations of evidence and coverage, not hidden hypotheses or unresolved mathematical dependencies of this proof. Parent alone determines any later adoption or disposition outside this correctness role.

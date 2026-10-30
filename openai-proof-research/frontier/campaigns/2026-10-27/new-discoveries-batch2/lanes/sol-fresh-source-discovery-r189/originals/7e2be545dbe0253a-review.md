# Independent full W5 proof review r1

**Verdict: PASS_FULL_W5. Blocking mathematical failures: none.** This is the independent full proof gate for the unchanged original target, not a contribution/eligibility verdict, formal certification, manuscript approval, external peer review, acceptance, count change or publication. I authored none of the W5 source, candidate or comparison components.

Myeongjin Kang; no affiliation. Original review prose CC BY4.0; original verifier code MIT. Third-party sources remain private in the externally referenced author packet.

## Identity and exact conjunction

The author packet fresh-analytic-discovery-r25 is authenticated at manifest SHA25610665dc832a51bca7651cbb091951b8b3ae3a7442339a64fd3b69e4b9743c606, scope bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03 and candidate2fd9649ae04c531eca486848917cbc3dc7ddfffdac9881ff1742594d2060147d. Its read-only verifier passed69 payloads,11 contextual inputs,35 pinned text blobs and5 retained primary files. I separately recomputed all35 Git blob hashes against the root complete preprints-tree, not its truncated alternative. The relevant source family has13 non-PDF blobs:12 retained author blobs and an unretained references.bib. This is explicitly recorded; no missing theorem-bearing body is being concealed as complete acquisition. Identity is not proof.

The reviewed claim is: there exist one nonempty contractible domain M⊂C³, a smooth geodesically complete Kähler metric g on M, and finite0<A≤B with −B≤K_g≤−A<0 on every real tangent two-plane; this same M admits a bounded holomorphic embedding into C⁵, while every bounded holomorphic M→C³ has **at least one point** where its complex Jacobian determinant is zero. The latter is not a claim of identically zero Jacobian. Embedding includes injectivity, immersion and homeomorphism onto the image. There is no properness or C⁴ claim.

The original scope candidly says it was frozen after preliminary feasibility. The hashed mechanism checkpoint already contains the prospective products/map. I read that checkpoint, the pre-freeze comparison and freeze receipt; their recorded chronology is consistent with this description. Hash receipts bind the versions but are not independent trusted timestamps. No full-scope weakening occurs in the final proof.

## 1. Actual source interfaces and order of choices

Source truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. I read the actual relevant statements, not just the catalogue. Source peaks:polynomial and peaks:bounds give homogeneous holomorphic P_k with uniform |P_k(z)|≤C_P|z|^k; positive degrees imply P_k(0)=0. The construction fixes1<a<2 and epsilon>0, then spacing/degree data with d3=d2/2>0, and then a sufficiently large integer Q≥4. The required degree thresholds are included in the source's final assembly.

Source base:convergence holds for **every finite L>0**, base:minorant whenever L>5logQ/d3, and base:chart-estimates for every fixed finite L>0. The final paragraph of Section6 explicitly permits chart constants to depend on the fixed L and chooses the metric parameter lambda only afterward. There is no smallness or upper-bound constraint preventing the integer choice. For instance choose L=floor(5logQ/d3)+1, a finite positive integer. Fix this L and phi=psi+L sum U_j before any added embedding parameters.

The actual metric:transfer proposition applies to this phi with finite centered-chart constants and gives the same M_phi, contractibility, a smooth geodesically complete Kähler metric, and two uniform strictly negative real-sectional bounds for one fixed sufficiently large lambda. The actual map:obstruction lemma gives no bounded C³ map with nowhere-vanishing determinant, using the same phi. These conclusions are imported, not re-audited upstream. They are not inferred from the differently quantified one-sided companion, whose Liouville example has curvature unbounded below and is a different domain.

M_phi is open because phi is smooth and the defining inequality is strict, and it contains(0,0). No later operation changes phi, the domain or lambda.

## 2. Scalarization and infinite products, independently rederived

Write s=epsilon²>0 and c0=a/(1+s)>0. Put kappa=(1+s)²/(a²s), rho=c0/2 and eta_j=2^−j. For |t|<rho, |eta_j t|<c0/4, so c_j(t)=c0+eta_j t never vanishes. The reciprocal substitutions used later are therefore defined on the whole parameter disk.

I checked the complex Cauchy–Schwarz step with no real-coefficient restriction. The identity

    1−cP = (c/a)(1−aP) + ((1−c/a)/epsilon)epsilon

implies |1−cP|²≤(|c/a|²+|1−c/a|²/s)(|1−aP|²+s). For c=x+iy, completion of the square gives

    (1+s)(s(x²+y²)+(a−x)²+y²)
      = a²s + ((1+s)x−a)² + (1+s)²y².

Dividing by a²s proves exactly

    (1+s)(|c/a|²+|1−c/a|²/s) = 1+kappa|c−c0|².

Thus the regularized denominator1+epsilon² is accounted for, and there is no missing constant>1 repeated at every factor. The estimate holds for every complex P and c, including zeros and cancellation configurations.

For each compact K⊂B² choose0<r<1 containing its norm radii. Uniformly over t in the entire open disk, the sums of |c_j(t)P_j(z)| are bounded by (c0+rho)C_P sum r^(Q^j)<infinity. This is sufficient for a uniform Cauchy argument for the finite products: a tail product differs from1 by at most exp(sum tail absolute values)−1, and prefix products are bounded by the exponential of the total sum. Consequently q_t exists locally uniformly in z, is holomorphic, and q_t(0)=1. No global compact-open estimate has been silently assumed here.

Fix z and t. If one factor is zero, the limit is zero. Conversely, if no factor vanishes, take a tail on which all |c_j(t)P_j(z)|≤1/2. The principal power-series logarithms satisfy |log(1−u)|≤2|u| and sum absolutely. The tail product is their exponential and is nonzero; the finite prefix is also nonzero. Thus a zero of q_t comes from an individual factor. No global logarithm of q_t or of all its factors is asserted.

For the finite products, multiply the exact scalar estimate and use1+x≤exp(x) for x≥0. The perturbation loss is at most exp(kappa|t|² sum eta_j²), and sum eta_j²=1/3. Passing to the limit at each fixed z uses the just-proved product convergence and the stipulated locally convergent logarithmic series. It gives

    |q_t(z)|² ≤ C0 exp(sum U_j(z)),  C0=exp(kappa rho²/3)<infinity,

for **every** z∈B² and **every** |t|<rho with the same C0. The globality comes from this finite-product inequality with a uniform loss, not from exchanging a boundary limit with local convergence. The sum of U_j is finite at every interior point. No representing-measure/Jensen premise enters this deduction.

## 3. One triple of products avoids every common zero

For each ordered index triple(j1,j2,j3), the three P_j in two variables are algebraically dependent. Indeed, distinct formal monomials of total degree≤m in three indeterminates number binomial(m+3,3), whereas their substitutions have degree≤mD in two variables and span a space of dimension at most binomial(mD+2,2), where D is a fixed finite bound for this triple. Cubic growth eventually exceeds quadratic growth. A nontrivial linear dependence gives a genuinely nonzero formal polynomial R_J with R_J(P_j1,P_j2,P_j3)=0. Repeated indices and even identically zero P_j do not invalidate this counting argument; no uniform bound on the relation degrees is required.

On T=D_rho³, each map t_l↦1/(c0+eta_jl t_l) is injective holomorphic with nonzero derivative and a holomorphic inverse on its image; its denominator has no zeros. Its image is a nonempty open subset of C. The three coordinates use **independent** parameter variables, even if the indices repeat. Their product therefore has nonempty open image in C³. A nonzero polynomial R_J cannot vanish identically on that image. Hence H_J is holomorphic and nonidentically zero on connected T; its zero set is closed relative to T and has empty interior.

T is nonempty and Baire, as a locally compact Hausdorff open subset of Euclidean space. The ordered triples are countable, so a point(t1,t2,t3) exists outside the union of all these nowhere-dense zero sets. This avoids countably many factor-index conditions, not an impermissible enumeration of uncountably many base points.

If all three selected q_tl vanished at some z, the exact zero characterization would provide a factor index jl for each l. The corresponding values of P_jl(z) would equal their reciprocal parameter targets, making H_J(t1,t2,t3)=0 by the polynomial relation. This is a contradiction. A single parameter triple consequently excludes simultaneous zeros on the entire ball, without a compact exhaustion or a later parameter adjustment.

## 4. Weighted coordinates and a full embedding of the same domain

The previously fixed L is a positive integer. Thus f_l=q_tl^L is single-valued holomorphic through its zeros; the three f_l still have no common zero. Raising the global product bound to L gives

    |f_l|² ≤ C0^L exp(phi−psi).

For every(z,w)∈M_phi, multiplying by |w|² and using |w|²exp(phi)<1 yields

    |w f_l(z)|² < C0^L exp(−psi(z)) = C0^L(1−|z|²).

This remains valid when f_l(z)=0. Therefore F=(z1,z2,w f1,w f2,w f3) is holomorphic and |F|²≤max(1,3C0^L) everywhere. No boundedness of the f_l by themselves, no bounded fiber radii, and no uniform lower bound on max_l|f_l| is needed.

Equality of two F values first gives equality of both base coordinates. At that base point some f_l is nonzero, forcing equality of w. For the differential, a kernel vector(u,v) has u=0 from the first two coordinates; then v f_l=0 for all l forces v=0. Thus the map is injective and a complex immersion of rank3 everywhere.

Injection and immersion alone would not settle the specified topology. Here each O_l={z:f_l(z)≠0} is open, their union is B², and the subset of F(M) with base coordinate in O_l is relatively open. On that subset the inverse is explicitly(Z,Y)↦(Z,Y_l/f_l(Z)), the restriction of a holomorphic, hence continuous, map on O_l×C³. The formulas agree on overlaps and cover the image. Consequently the inverse is continuous globally and F is a homeomorphism onto its image. No properness assertion is used.

All these functions are constructed after M_phi and its metric are fixed. They do not alter a source parameter or take a limit of metrics. The same nonempty contractible M thus satisfies the complete pinched-metric conclusion, the bounded C⁵ embedding, and the bounded C³ Jacobian-zero obstruction. Each individual f_l may have zeros; empty common intersection is fully compatible with the source obstruction against one globally nonvanishing weighted determinant.

## Findings and gate boundaries

Every new analytic, algebraic, category and topological deduction required by the full scope is valid. No numerical sampling, generic bounded projection theorem, bounded Cartan division, upstream curvature reproof or unproved weighted-generation theorem was used. The elementary ingredients above suffice. No repair or narrowed target is needed.

The proof does not determine whether the construction is a substantial contribution rather than a technical application of explicit source factors. That is a separate gate. It also proves neither C⁴ impossibility, optimal dimension, proper bounded embedding, quantitative inverse control nor Caratheodory completeness. The full original W5 conjunction, and only that conjunction, receives PASS_FULL_W5.

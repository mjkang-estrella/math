# Sustained routes and eligibility gates

This is an investigator record, not an acceptance or a Lean certificate. All counts remain 39 prior plus 13/20 current. The numerical checks are diagnostics only.

## 342633: a complete stationary-energy proof, then exact prior-art exclusion

Let Q be the finite irreducible CTMC generator, π its stationary probability row vector, D=diag(λ_i) nonnegative and nonzero, and A=D−Q. The standard killed-chain inverse exists, and h=A⁻¹1. Put λ=Σπ_iλ_i>0. Proposition 2.2 and equation (6) of the source identify the event-stationary SCV as 2λπh−1. We do not claim to have formalized that probabilistic identity.

Multiplying Ah=1 by π gives Σπ_iλ_i h_i=1. Multiplying componentwise by π_i h_i and summing gives

Σπ_i h_i = Σπ_iλ_i h_i² + (1/2)Σ_{i,j}π_i q_ij(h_i−h_j)².

The identity follows by expanding the square and using both Σ_j q_ij=0 and Σ_i π_i q_ij=0. Off-diagonal terms are nonnegative and diagonal square terms vanish, so πh≥Σπ_iλ_i h_i². Weighted Cauchy–Schwarz now gives

1=(Σπ_iλ_i h_i)²≤(Σπ_iλ_i)(Σπ_iλ_i h_i²)≤λπh.

Consequently SCV≥1, including zero individual arrival rates. No reversibility is assumed. Equality forces the Dirichlet sum to vanish. Irreducibility and π_i>0 make h constant along every directed edge and hence everywhere, so Ah=1 forces all λ_i equal. Conversely equal rates give equality.

The finite search checked 81 two-state and 512 three-state strictly positive rational-rate instances exactly, all consistent with the proof. Attempts to exploit strongly directed cycles fail for precisely the stationary-energy identity, rather than because symmetric examples are representative.

**Decisive exclusion:** Qi-Ming He, J. Applied Probability 58 (2021), 880–889, DOI 10.1017/jpr.2021.18, Theorem 3.2 states the exact SCV conclusion, including equality, and section 4.1 explicitly applies it to the event-stationary MMPP. Theorem 3.1 and its proof establish π(D−xQ)⁻¹1≥1/λ without reversibility; Theorem 3.2 derives the moments, and section 4.1 supplies the same PH bridge. Read the retained `sources/he-2021.txt`, lines 304–397 and 471–494. This is a full-scope known result. The authors' 2018 paper is withdrawn (live abstract receipt retained); its v1 is NOT used as a valid prior proof. Its sign-preservation assertion for multiplication by a nonnegative inverse would not justify the claimed coordinate signs. The 2021 proof removes any need to adjudicate that old argument. No Lean investment or credit is warranted.

## 345310: the general connected-Hopf framework subsumes freeness

The pattern algebra is the linear span of pattern-count functions inside functions G(h)→k, with pointwise multiplication. It is therefore commutative, regardless of whether the presheaf multiplication is commutative. The coefficient field has characteristic zero (source section 2). The source's Theorem 1.4 equips it with the coproduct dual to object multiplication and an antipode when h is connected. By object size the coproduct is graded: a factorization a=b*c has |a|=|b|+|c|. Its degree-zero coalgebra is k, so it is a connected coalgebra; the reduced iterated coproduct of an object of size n vanishes after n positive factors. Thus the associated Hopf algebra is commutative and connected in the *coalgebra* sense, not just as a ring or topological space.

C.-C. Li and G.-S. Zhou, `arXiv:2109.01882v2`, Corollary 3.5: every commutative connected Hopf algebra over a characteristic-zero field is a polynomial algebra over any Hopf subalgebra. Take K=k. This proves precisely free commutative generation, the definition of free used in the pattern paper. No finite GK dimension, affine hypothesis, finite number of objects, or commutative presheaf multiplication is necessary. Their Corollary 3.4 gives a filtered ordered-monomial basis by lifting generators from the coradical associated graded; commutativity turns that basis into the polynomial isomorphism. The proof of 3.4 and deduction of 3.5 were read in `sources/2109.01882.txt`, lines 650–676.

This settles the route by a routine specialization of an explicit published general theorem. It is ineligible under the user's standard even if the original paper continues to label it a conjecture. This does not assert existence of a particularly natural combinatorial generator basis. The source's convention is connected associative presheaves when forming Hopf algebras; dropping connectedness merely to fabricate a counterexample is prohibited.

## 340663: truncated-binomial moment route, no qualifying endpoint

The source preceding Conjecture 3.3 uses b_n=n. For this reading and each *fixed positive integer* k, the nth summand Y_n has law Bin(n,1/2) conditioned on Y_n≤m_n=floor(n/k), independently across bins. The following ordinary proof establishes the Lyapunov condition with δ=2 under those hypotheses. The conjecture sentence alone does not repeat the bin-size and k quantifiers; scope recovery must be reviewed before any exact claim.

For k≥3 put r=1/(k−1)<1 and Z_n=m_n−Y_n. Consecutive binomial weight ratios below m_n are at most r, hence P(Z_n=j)≤r^j. Normalization also gives P(Z_n=0)≥1−r. If n≥2k, m_n≥n/(2k), so m_n/(n−m_n+1)≥1/(4k) and P(Z_n=1)≥(1−r)/(4k). Therefore Var(Y_n)=Var(Z_n)≥P(Z_n=0)P(Z_n=1)≥(1−r)²/(4k). Also E Z_n⁴≤Σj⁴r^j<∞, uniformly in n. Jensen and |a−b|⁴≤8(a⁴+b⁴) give E|Y_n−E Y_n|⁴≤16Σj⁴r^j. Thus the fourth-moment Lyapunov quotient is O(N)/Ω(N²)→0.

For k=1 the ordinary binomial variance is n/4 and fourth centered moment is (3n²−2n)/16. Summing yields the quotient O(N³)/Ω(N⁴)→0.

For k=2 set B_n~Bin(n,1/2), T_n=2(B_n−n/2)/sqrt(n), and condition T_n≤0. The ordinary binomial CLT gives T_n⇒Z~N(0,1). The conditioning event has probability tending to 1/2, and E T_n⁴=3−2/n≤3 gives uniform integrability for first and second moments. Therefore the conditional variance tends to Var(Z|Z≤0)=1−2/π>0. Consequently Var(Y_n)~n(1−2/π)/4. Conditional fourth moments of T_n are bounded, so centered fourth moments of Y_n are O(n²). Again summation gives Lyapunov quotient O(1/N).

This route is a standard truncated-binomial application of CLT and geometric-tail estimates, not demonstrated new-to-literature mathematics. The exact rational computation covered k=1..20, n=1..400, displaying cumulative ratios at N=50,100,200,400. It cannot certify an infinite limit. No Lean surrogate theorem is supplied. To qualify, one would need exact source-scope recovery, a successful novelty/significance argument overcoming the routine-probability framework, and a literal formal limit theorem with all distribution and independence bridges. Currently zero credit.

## Other attempted mechanisms

* 346005: from the exact arithmetic product and quotient, f_k(n)=(n−k/2+1)/2 if n≡k/2−1 mod 2, and 3n+3k−5 otherwise, for even k. Exhaustive finite orbits on k=−40,−38,...,40 and n=−100,...,100 all eventually repeat within 161 steps. The source's own 17→52→... example fixes the intended *eventual* periodicity; failure to return to the initial point is only a wording defect and is not pursued. At k=2 this contains classical integer Collatz eventual periodicity. No exact escape construction survived.
* 343051/343052: exact recursive divided differences for key polynomials and exact semistandard tableaux for skew Schur polynomials, followed by M-convex support exchange and characteristic-polynomial inertia of every normalized quadratic derivative, produced no violations. Published full-scope theorems now close both routes. Characteristic-polynomial sign variation counts positive roots exactly because the Hessian is real symmetric; these are not numerical eigenvalue tests. The two initial SymPy Boolean conversion failures are retained in logs; the corrected final run completes.
* 340460: exhaustive graphs to order 5 and exhaustive balanced-complex witnesses on the same labelled vertices pass over F2. This tests the actual CM condition through all link homologies, rather than flagness alone. The literature's theorem about a matching h-vector without preserving dimension does not automatically give a matching f-vector, so it is not an exclusion. Extending to six vertices requires a more selective witness method, rather than enumerating all simplicial complexes without a cap.
* 346380: the source explicitly says its nonalgebraic-diagonal obstruction fails at the rational squared diagonals relevant to (2,2,1). Substituting that corollary is invalid. No spatial unit-triangle realization or complete topology enumeration was obtained. A planar area obstruction would not address spatial domes.

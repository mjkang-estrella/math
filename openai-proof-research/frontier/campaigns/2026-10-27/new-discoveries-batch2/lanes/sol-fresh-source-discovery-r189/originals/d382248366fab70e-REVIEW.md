# R162BC7 independent full correctness review

Verdict: **PASS**, relative to stipulated Source135 operative truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. This certifies the entire unchanged frozen statement and its submitted mathematical proof. No required repair or unresolved essential mathematical dependency remains. It does not assign a contribution grade, acceptance, or count. Campaign context remains 19/20, latest R041.

Target identities: STATEMENT.md is 2250 bytes, SHA256 ffb70a869024e8ebf88964edb0a41575d2d3922976579e93dd593a2d4ed3f528. PROOF.md is 23940 bytes, SHA256 dc51e6cc034a28da0f229bae81f85a00eee98be03d3dc9afe26521165f055fca. These identify the original author files, not a repaired version. I read all seven proof sections and the complete statement, FINAL, SOURCE-COMPARISON, READING-LIMITS, PREFREEZE, WORKING, and freeze metadata. The author’s assertion of completeness was not evidence for this verdict.

The certified target is the existence of ONE absolute integer n0>=2 such that, for EVERY characteristic-zero field K and EVERY integer n>=n0, EVERY frozen-model syntactically homogeneous seven-computational-layer Sigma-Pi-Sigma-Pi-Sigma-Pi-Sigma circuit computing the formal endpoint IMM(n,n) needs at least n^(n^(1/4)/20000) computational gates. Including leaves can only increase size. All ambient n^3 variables, arbitrary bottom support, free scalar sum-edge coefficients, arbitrary finite fan-in/out, sharing, repeated occurrences, unary/empty gates, constants and zero-polynomial formal-degree conventions remain as frozen. Neither a formula nor a set-multilinear circuit replaces this class.

## 1. Independent reconstruction of parameters and one rank map

Take t=floor(n^(1/4)); thus t^4<=n<(t+1)^4. Write sigma=1-1/t+1/t^3, lambda*=sigma/(1+sigma), k=floor(n lambda*), m=n-k, lambda=k/n and rho=k/m. For all sufficiently large t, k,m are between fixed positive multiples of n, 0<rho<1, and rho=sigma+O(1/n), with rho<=sigma because x/(1-x) is increasing. Consequently 1-rho=Theta(1/t), and s=m-k is positive with 0<s/k<1. No parity assumption or subsequence is used.

The exact integers v=kn^2,u=mn^2 retain the inactive endpoint variables. For a=ceil(v/(t-1)), the logarithmic derivative of x/(x+v) is at most 1/x; consequently alpha=a/(a+v) lies in [1/t,t^(-1)exp(C/a)]. For b=ceil(u alpha^rho/(1-alpha^rho)), the same argument gives alpha^rho<=beta=b/(b+u)<=alpha^rho exp(C/b). In particular a,b=Theta(n^3/t), beta<=2/t eventually, and q=alpha^((1+rho)/2) satisfies 1/t<=q<=2/t. Because the proportionality constants can be numerical throughout, these assertions are uniform in the field and circuit. They imply a>=k, 4n<=min(a,b) and occupation error O(n^2/a+n^2/b+n^2/v+n^2/u)=O(t/n). The harmless intermediate-space correction (1-1/(a+v))^(-n)<=2 is uniform as well.

Fix this single k,m,a,b, and the schedule in section 5. The rank map throughout is g_[k,m](partial_V,U) from H_V(a) tensor H_U(b) to H_V(a-k) tensor H_U(b+m), with D=h(v,a)h(u,b). It is linear in g and has subadditive rank. The circuit estimate is uniform in the partition and therefore applies to this very schedule, not a different partition or measure.

For a product of positive-degree homogeneous factors with total degree n, expand bidegrees i_j,e_j-i_j with sum i_j=k. Set delta_j=i_j-lambda e_j. Their sum is zero. Differentiation in V commutes with multiplication in the disjoint U variables, so the positive-delta factors may act first. If their total bidegree is I,J, then I<=k<=a and J<=m. The intermediate dimension divided by D is at most

    (a/(a+v-1))^I beta^(-J)
      <= 2 alpha^(I-rho J)
      = 2 q^(sum_j |delta_j|).

Both binomial-ratio bounds have the claimed directions. This is a dimension-of-image upper bound, not a false assertion that the finite bidegree-projected rank map is multiplicative. Sum over bidegree assignments and then drop the sum constraint to obtain 2D product H_e. This derivation works over every field, with arbitrary factor coefficients and support.

## 2. Nearest integers and every degree band

For 0<q<=1/2, the two tails of the integer geometric series give H_e<=q^d(1+4q^(1-2d))<=5, where d=dist(lambda e,Z). A tie is covered by retaining one nearest integer and bounding the other in the tails. The potentially dangerous small distance is not paid by a fixed constant at every factor.

Specifically let d0=1/(16t). The logarithm of q^(1-2d)/d has second derivative 1/d^2>0, so its maximum on [d0,1/2] occurs at an endpoint. The endpoint bounds are 64 and 2, using q<=2/t and log(1/q)<=log t. Hence 4q^(1-2d)<=256d. Once L=log(1/q)>=512,

    H_e <= exp(-Ld+256d) <= q^(d/2).

L>=512 requires an extremely large absolute threshold. This is permitted by the exact existential n0; finite small-t behavior does not refute it.

For the first degree band, put lambda0=(t-1)/(2t-1). Exactly,

    lambda*-lambda0 = 1/[t^3(1+sigma)(1+(1-1/t))].

For t>=4 this lies between 1/(4t^3) and 1/(3t^3). For t^2/2<=e<t^2, h=e(lambda-lambda0) is at least 1/(8t)-1/t^2>=1/(16t) when t>=16, and at most 1/(3t). If lambda0 e is integral, h is its distance to the nearest integer since h<1/2. If it is nonintegral, its grid denominator 2t-1 gives distance at least 1/(2t-1); the distance function is 1-Lipschitz, so after displacement the distance is at least 1/(2t-1)-1/(3t)>=1/(6t). This also covers displacement across the nearest-grid-point midpoint.

For t/2<=e<t, lambda0 e=e/2-e/(4t-2). For even e the distance is at least 1/8 and less than 1/3. For odd e the distance exceeds 1/6 for t>=4. The positive displacement is at most 1/(3t^2), yielding distance at least 1/16 eventually. For e=1, lambda<1/2 and tends to 1/2, so the distance is lambda>=1/3 eventually. Floors in n lambda* and in n^(1/4) have both been charged; no favorable values of n are selected.

## 3. Shared-gate occurrence expansion

Induction on gates shows that every nonzero value at formal degree d is homogeneous of actual degree d. The nonzero output therefore has formal degree n. A zero polynomial retains its formal degree, but a vanishing summand/product may be omitted in an algebraic expansion. Degree-zero values are field scalars. Arbitrarily many repeated degree-zero inputs change this scalar, not a branching count. No algorithm for detecting zero gates is claimed or needed.

Repeated additive edges from a given computational predecessor combine into one scalar coefficient, leaving at most S distinct predecessors. Product edges do NOT combine in this way; their occurrences and degrees remain counted with multiplicity. The top sum supplies at most S product terms.

For a term whose middle factors all have degree <t^2, successively group two factors below t^2/2. Group degrees remain <t^2. At termination at most one is below t^2/2. If r others remain, total degree n<(r+1)t^2; n>=t^4 supplies at least t^2-1 band factors (indeed the strict inequality supplies a little more). Select exactly t^2-1 and collect all other factors into one homogeneous remainder. This is algebraic grouping, not construction of additional circuit gates.

Otherwise select just one occurrence of a middle sum of degree >=t^2 and distribute that one occurrence over at most S predecessor products. For each resulting branch, if all its lower sums have degree <t, the same grouping at threshold t gives at least t-1 factors in [t/2,t). Collect everything else, including factors outside the chosen middle sum, into ONE remainder. If instead a lower sum has degree >=t, expand just one occurrence over at most S bottom products. Every nonzero positive-degree bottom sum is a homogeneous linear form, even with full ambient support. Hence a nonzero resulting bottom product of degree >=t supplies at least t degree-one occurrences; all others join the one remainder.

The expansion tree has at most S choices at each of three additive stages. Early termination does not add separate S+S^2+S^3 budgets: a tree of height at most three with branching at most S has at most S^3 leaves. Other occurrences of any selected shared gate remain unexpanded in the remainder. There is thus no wire-size, fan-out, or formula-size assumption. Empty or unary gates introduce no exceptional positive-degree branch, and arbitrary scalar coefficients multiply the outer summand only.

The distinguished distances sum to at least t/32 in all three cases. Apply H_e<=q^(d_e/2) to each distinguished factor and H_e<=5 once to a positive-degree remainder. There is no charge for a degree-zero remainder after scalar absorption. Together with the product-rank factor 2 this gives

    R(g)<=10 S^3 D q^(t/64)<=10 S^3 D t^(-t/128).

The actual primary AGKST Lemma 4.1 is a FORMULA statement. Its complete v1 and current proofs were read. It motivates the bands; its formula-size bound is not silently used for arbitrary shared circuits. The preceding direct occurrence argument verifies the needed extension.

## 4. Occupation, trace and normalization reconstruction

In the complex homogeneous spaces choose z^M/sqrt(M!) orthonormal. A path contributes coefficient sqrt(product_V M_i product_U(M_i+1)) and signed unit-coordinate shift epsilon_P. The shifts determine each layer’s edge and therefore the path uniquely. For a fixed input, different paths reach different outputs, proving the first trace identity with one factor D.

For a uniform weak composition of h into r coordinates, coefficient extraction from product d_i! y^(d_i)/(1-y)^(d_i+1), divided by binom(h+r-1,h), gives E product(M_i)_(d_i)=(h)_H product d_i!/r^(overline H). Independent geometric coordinates of mean h/r have factorial moments (h/r)^H product d_i!. The ratio is product_(j<H)(1-j/h)/(1+j/r), at most one. For H<=H0<=h/2 its logarithm is at least -H0^2/h-H0^2/(2r). This extends termwise only when falling-factorial coefficients are nonnegative; all uses here meet that condition. H>h gives zero, and H=0 is harmless.

The first trace therefore satisfies T>=D n^(n-1) mu exp(-Ct/n)>0, with mu=(a/v)^k(1+b/u)^m. Inactive coordinates remain in the compositions; they are never removed to improve a normalization.

For the second trace, write the entry of F*F indexed by M,M' as a sum over P,Q with M+epsilon_P=M'+epsilon_Q and square it. The second pair R,S must have the SAME difference. Thus M'=M+epsilon_P-epsilon_Q is determined; there is no additional independent average or D factor. Since the matrix entries are real nonnegative, squaring these entries gives the stated four-path formula.

At one layer, e_p-e_q=e_r-e_s means either N: p=q=i,r=s=j, or D: p=r=i,q=s=j,i!=j. The all-equal case belongs to N. The local products are M_i M_j or M_i(M_j+1) in V, and (M_i+1)(M_j+1) or (M_i+1)M_j in U. If M' is invalid, in a V-D layer M_i=0, or in a U-D layer M_j=0, and the relevant polynomial vanishes. Unavailable N derivatives also vanish. Different layers use disjoint coordinates, so no cross-layer negative-index failure is omitted.

Repeated N coordinates give z^2=(z)_2+(z)_1 and (z+1)^2=(z)_2+3(z)_1+1. All remaining polynomials are products of nonnegative factorial-coefficient expressions on distinct coordinates. Hence upper comparison to independent geometric occupations applies in both groups. Dividing by A^2 for V and (1+B)^2 for U gives N weight 1+c_j 1_(i=j), D weight c_j, with c_j=alpha^(-1) in V and beta in U. The total normalizer is mu^2. Ordinary unweighted monomial traces would be different; they are not used. The integer matrix in section 6 is used solely for rank transfer after a basis change.

## 5. Joint collision count, decoration and all intervals

Relax each D inequality i!=j, retaining its nonnegative assigned weight. Newly admitted tuples need not have their genuine occupation expectation; this is explicitly an upper bound. Expand every N equality correction, in BOTH variable groups. The states become N=(PQ)(RS), D=(PR)(QS) and E=(PQRS), with weights 1,c_j,c_j. All-equal quadruples may occur in multiple relaxed/decorated states; positive overcounting is intentional, not a disjoint-partition assertion about the original trace.

At an internal vertex, the join of adjacent layer partitions has two blocks exactly for NN and DD. Every other adjacency, including EE, has one block. Boundary labels are fixed to one. Complete matrix layers impose no additional restriction between vertices, so the exact count for a fixed state word is n^(2(n-1)-b(omega)). This verifies (5.1), including adjacent equality corrections.

Fold each E to D. Boundary N-D edges have the same one-label cost whether the D was decorated or not. Inside a resulting D run of length ell, an edge incurs an additional 1/n precisely if at least one endpoint position was E. Each decorated position except the first injects into its own preceding internal edge, proving j(A)>=|A minus {first}|. Therefore the sum of decoration factors is <=2(1+1/n)^(ell-1). This covers ell=1, initial/final runs, and the all-D word as one run. Across all runs the total is <=exp(1) 2^(number of runs); the all-N word has just one preimage. No assumption of independence of adjacent corrections is made.

For the scheduled chunks V U^(1+floor(is/k)-floor((i-1)s/k)), all lengths are 1 or 2 and the counts are exactly k,m. Consecutive full chunks have discrepancy rho(rs/k-E)<rho. An arbitrary interval is a proper terminal chunk part (only U, nonpositive discrepancy), full chunks, and a proper initial chunk part (discrepancy <=1), or lies in one chunk. Thus EVERY interval satisfies d(I)<=1+rho, with the entire word having discrepancy zero.

A D run has weight alpha^(-d(I)) exp(C #U(I)/b)<=t^2 exp(C #U(I)/b). This remains true for negative d(I), since alpha<1 and the expression is monotone in d(I). Runs are disjoint, so the total ceiling error is exp(Cn/b), not one full error per run. For mixed words with r interior D runs and e in {0,1,2} endpoint D runs, switch count is 2r+e, and at most 2 binom(n-1,2r+e) words have these counts. Multiplying switch cost, run weights and 2 per run yields the bound

    2(2t^2)^(r+e)/(2r+e)! exp(Cn/b).

Summing gives at most 2(1+2t^2+4t^4)exp(sqrt(2)t+Cn/b). The constant N word contributes one; the constant D word contributes <=2exp(Cn/b), using rho m=k. Both have zero switches and are treated separately. Absorbing polynomial factors gives T2<=D n^(2(n-1)) mu^2 exp(Ct). Positive-semidefinite Cauchy–Schwarz now yields rank_C(F)>=T^2/T2>=D exp(-Ct).

## 6. All fields, exact exponent, and threshold

The ordinary-monomial matrix F_IMM has integer entries, since IMM has integral coefficients and derivatives have integer falling-factorial coefficients. Its complex rank agrees with its rational rank and with its rank over every characteristic-zero K: precisely the same integer minors vanish. An arbitrary characteristic-zero field need not embed in C. No such embedding, coefficient-height bound, or representation of its circuit coefficients is assumed. This transfer affects only the fixed hard polynomial; the circuit upper bound was valid directly over K.

Combining the two ranks on the SAME finite spaces gives log S>=t log t/384-Ct/3-log(10)/3. Eventually t>=n^(1/4)/2 and log t>=log n/5. Since the losses are O(t) and the positive term is Theta(t log t), their ratio tends to zero. After one further numerical threshold, log S>=n^(1/4)log n/7680, which is stronger than the exact frozen 1/20000 exponent. Every threshold is numerical and there are finitely many of them; their maximum is one absolute integer n0 independent of K and the circuit. No explicit small-n bound is asserted. Counting leaves cannot reduce the computational-gate lower bound.

## 7. Objections considered and disposition

No counterexample or invalid inference requiring repair was found. Specific adversarial issues were:

- Formula-only primary decomposition versus shared gates: discharged by the direct S^3 occurrence proof, with product multiplicity and additive coefficients distinguished.
- Fixed per-factor errors when distances are O(1/t): discharged by the log-convex endpoint calculation and the allowed large absolute threshold.
- Floors destroying the small positive perturbation: discharged by e/n<=1/t^2 and the rational-grid distance argument for all n in each floor block.
- Treating a finite projected map as multiplicative: avoided by bidegree expansion before commuting operators and using intermediate dimensions.
- Losing a factorial or a factor D in traces: discharged by the orthonormal calculation and determined M' identity.
- Assuming composition-coordinate independence or ignoring negative shifted occupations: discharged by exact factorial moments and the local zero factors.
- Separating adjacent V/U collision events: avoided by the three-state vertex-partition count before folding.
- Failing on a singleton run, endpoint run, all-E, or all-D word: covered by the initial-position allowance in each run and separate constant-word bounds.
- A prefix-only schedule estimate: the proof supplies all intervals via two partial chunks and complete chunks.
- Different parameters on circuit and hard sides, or a K-to-C embedding: neither is used.
- Finite tests as proof: excluded. The small checks described below only detect implementation/normalization mistakes; the derivations above apply universally.

In particular, there is no auxiliary-lemma counterexample being misrepresented as a refutation of the eventual theorem with unknown n0, and no remaining finite auxiliary defect to repair.

## 8. Dependency ledger and limits

Stipulated source: the complete actual Source135 eleven texts, authenticated against the complete pin tree, provide the rank-map/product interface (eq:rank-map, lem:product-rank), occupation identity (lem:occupation-moments), four-path and local-weight identities (eq:four-path-trace, eq:local-polynomials, eq:local-weights), all-interval scheduling operation (eq:interval-discrepancy), and integer-minor transfer (cor:characteristic-zero). I read their operative proofs and their hypotheses. The entire paid depth-five lower bound and all-field upper bound (prop:upper) were also read. They are not substituted for the seven-layer target and their truth is not audited.

Actually checked primary interfaces: AGKST’s complete formula-decomposition proof in v1 and current versions; current residue/product lemmas and their deferred claims; current stronger IMM statement and word-polynomial proof; ICALP numbering and hypotheses; LST actual set-multilinearization, weighted homogenization, and word-ABP interfaces; Forbes complete own paper including integer-polynomial vanishing-minor transfer and constructive set-multilinearization. Bera–Chakrabarti and ABT theorem restrictions and selected operative proof sections were read. Precise actual extents are in READING-LIMITS.md and page-displays.jsonl. No claim of full reading follows for partially read works.

Elementary derivations checked here: all new parameter estimates and distance arithmetic; shared-gate expansion; the third-state partition count and folding inequality; run-sum budget; direct moment checks at the new parameters; positivity/rank inequality; minor preservation; final constant and single threshold. These are enough for every essential mathematical step. None depends on the unread portions of BDS, HY11, Minc’s original, or the transitive literature behind the nonessential primary comparisons. Those works remain unread, not presumed independently verified. No essential conditional interface remains unresolved. There is no full-paper/transitive/exhaustive literature or project-history certificate, and no contribution or priority judgement.

Bounded sanity: independently constructed the ordinary-basis operator for width 2, degree 3, schedule VUU, occupation totals a=2,b=1. With the factorial Gram weights, its traces T=200,T2=852 exactly match the independently summed local four-path table on 80 domain indices and 28 compatible path quadruples. Also checked 21 short-run decoration sums and 64 exact rational distance values, including a huge t=2^1024 solely as an arithmetic sanity case. These are not correctness gates or substitutes for the preceding proofs.

No history traversal was used; no sibling review, peer activity, findings, task status or aliases were inspected or queried. No author followup was requested. All original author bytes/modes remain unchanged. Parent alone integrates this verdict and any independent contribution result.

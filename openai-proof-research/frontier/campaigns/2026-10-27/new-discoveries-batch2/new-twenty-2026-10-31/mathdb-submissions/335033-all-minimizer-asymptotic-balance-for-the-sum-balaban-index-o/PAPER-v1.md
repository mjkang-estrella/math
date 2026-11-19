# All minimizing dumbbells have balanced asymptotic clique orders

MathDB working target 335033; exact owned arXiv:1701.02716v1 convention. Implementation paper v1, 2026-11-15 UTC. This paper accompanies a compiled and separately kernel-checked unconditional endpoint. It does not assert acceptance, originality, priority, journal-final equivalence, exact finite balancing, or minimization among all connected graphs.

## Statement and source convention

Let a,b,d be positive integers. Start with disjoint K_a, a path on b vertices v_0,...,v_{b-1}, and K_d; join every vertex of K_a to v_0 and every vertex of K_d to v_{b-1}. This includes b=1. Put n=a+b+d and require a≤d only to remove reversal. For a vertex u let w(u) be the SUM of its distances to all vertices. With m edges define

SJ = m/(m-n+2) Σ_{uv∈E} 1/√(w(u)+w(v)).

This is the sum-Balaban index. The ordinary Balaban index uses a PRODUCT in the denominator and is a different problem. Define Q=√2 log(1+√2)>0 and c=√(√Q)>0. For each n≥3 the admissible set is nonempty and finite, so a minimum exists.

**Theorem.** For every function f from natural numbers to triples which is eventually minimizing SJ among all admissible triples of order n, writing f(n)=(a_n,b_n,d_n),

a_n/√n → c, d_n/√n → c, b_n/n → 1.

No annulus, expansion, balance, subsequence-selection, or rate hypothesis is imposed on f. The source's existence assertion follows by choosing a minimum for each n≥3; the formal endpoint proves the stronger universal assertion. We claim neither Conjecture 9's exact finite balance d=a or a+1 nor global optimality over all connected graphs. The argument below claims only the three displayed limits.

The exact owned primary is Knor–Kranjc–Škrekovski–Tepeh, “On the minimum value of sum-Balaban index”, https://arxiv.org/pdf/1701.02716v1, Conjecture 10, printed page 11. Its cover has arXiv date 2017-01-10 and internal date 2021-08-26; both are retained. PDF SHA256: 75eab26d6b17856c4067380ea7ecadfe29819e87303df15bc85e3a5a7cfe575e. Binding and source reading are inherited qualifications, not fresh primary inspection in this implementation. The 2017 journal final and ordinary-Balaban 2016 predecessor bodies remain closed/unread, without reconstruction or identity claims.

## Exact graph identities and compactness bounds

Set S_1=a+d and S_2=a²+d². Direct counting gives

m=n-1+(S_2-S_1)/2, k=m-n+2=1+(S_2-S_1)/2>0.

Every vertex in the left clique has transmission L=a-1+b(b+1)/2+d(b+1); the right formula exchanges a,d. The path transmission is

W_i=i(i+1)/2+(b-1-i)(b-i)/2+a(i+1)+d(b-i).

With t=i+a this becomes W_i=t²-(n-1)t+n(n-1)/2-(S_2-S_1)/2. Also L-W_0=n-a-1, and the reversed identity holds at the right endpoint. These formulas count all clique-to-endpoint edges, not a single bridge per clique. The five edge contributions are the two clique interiors, the two attachment sets, and the path edges. They are formalized in Dumbbell, Distances, Transmissions, EdgeCounts and EdgeFormula.

For any connected n-vertex graph, w(u)≤n(n-1)/2: its jth positive distance in nondecreasing order is at most j, because a shortest path to a more distant vertex supplies every intervening level. Thus every edge term is at least 1/n and SJ≥m²/(nk). Bounded balanced trials imply a common bound on the minimum. Consequently m=O(n), k is bounded below by a positive multiple of n, and S_2/n lies in a compact interval bounded away from zero. The checked implementation gives, for every minimizing triple and n≥2048,

0≤a/√n≤32, 0≤d/√n≤32,
1/1024≤S_2/n≤512, n-b≤64√n.

These are theorems every_minimizer_radial_bounds and every_minimizer_annulus, with explicit finite trial bounds, not a restriction of the domain. In particular neither individual clique is assumed to grow; limits on the coordinate axes remain possible at this stage.

## Uniform two-term expansion

Put x=a/√n, y=d/√n, q=x²+y², e=1/√n, and define

F(q)=q/2+1+Q+2Q/q,
G(x,y)=(q+2)(x³+y³)/(2q)+(x+y)(-1/2+2Q/q²).

For fixed B≥0 and δ>0 there is a constant K, independent of a,b,d,n, such that whenever S_2≤Bn, δn≤S_2, n≥16(2B+4), and δ²n≥8B,

|SJ-F(q)-eG(x,y)|≤K/n.

Here is the complete estimate mechanism, including the endpoints. For each of the four clique or attachment square-root arguments A, the exact polynomials give |A-n²+2an|≤(B+3)n on the left, and the analogous bound with d on the right. Comparing with (n-a)² and using a²≤Bn gives |A-(n-a)²|≤(2B+3)n. The threshold ensures a≤n/4 and both arguments≥n²/4. The reciprocal-square-root perturbation identity bounds their inverse-root difference by 4(2B+3)/n². Moreover

1/(n-a)-1/n-a/n²=a²/((n-a)n²),

whose magnitude is at most 2B/n². Hence the per-edge error after 1/n+a/n² is at most (10B+12)/n². Weighting by a(a-1)/2 and a, and the right counterparts, gives the clique contribution

S_2/(2n)+S_1/(2n)+(a³+d³)/(2n²)+O(1/n),

with uniform explicit remainder ((B+1)(10B+12)+B)/n. All statements include cliques of order one.

For the path let φ(u)=u²+(1-u)²≥1/2 and h(u)=1/√φ(u). Its Lipschitz constant on [0,1] is at most 8, by the reciprocal-root difference identity and φ(u)-φ(v)=2(u-v)(u+v-1). The exact path polynomial gives the actual-edge/reference-sample discrepancy uniformly O(n^-2). Rectangle integration has error≤8/n; the omitted endpoint intervals have error at most 8 times the sum of their squared lengths. The integral is Q: an antiderivative is (√2/2)arsinh(2u-1), evaluated from 0 to 1. The b-1 samples, including the extra endpoint discrepancy of size 1/n, therefore give

path contribution = Q-S_1/n+remainder, |remainder|≤(20B+45)/n.

This proof remains valid when b=1; no interior path or positive normalized coordinate is presumed. Adding the five contributions yields

edge sum = q/2+Q+(a³+d³)/(2n²)-S_1/(2n)+error,
|error|≤E(B)/n, E(B)=(B+1)(10B+12)+21B+45.

Writing u=S_1/n and v=1/n, exact counting gives m/k=1+(2-4v)/(q-u+2v). Expansion around q yields

m/k = 1+2/q+2u/q²+error,
|error|≤P(B,δ)/n, P(B,δ)=2(4B²+8B+4)/δ³.

This follows by putting the rational difference over q²(q-u+2v); its numerator is 2u²-4vq²-4vq-4uv. Use u²≤2B/n and the lower bound on q; the stated threshold keeps the denominator away from zero. In the product the remaining mixed term has absolute value≤2B(B+1)/(δ²n), using 0≤(a³+d³)/n²≤Bu. Thus one valid uniform constant is

K=P(B,δ)(B+Q+E(B)+1)+(1+2/δ+2/δ²)E(B)+2B(B+1)/δ².

The exact conversion from rational variables to x,y produces precisely F+eG. All these inequalities and identities are the inherited checked chain ending in actual_SJ_rational_expansion. This implementation adds general_uniform_expansion to package its thresholds as an eventual bound. For minimizers common_uniform_expansion uses B=512, δ=1/1024 and N=2^40, covering the entire common annulus with a single K. No new analytic estimate is assumed.

## Rounded trials without numerical assumptions on Q

Let k_n=floor(c√n), and T_n=(k_n,n-2k_n,k_n). Positivity of c implies eventual admissibility. Put u_n=k_n/√n. The floor inequalities give

c-1/√n≤u_n≤c,

so u_n→c. The checked trial-cost identity gives eventually

F(2u_n²)-F(q_0)≤16/n, q_0=2√Q=2c².

It follows that eventually c²<2u_n²<2c²+1. Apply the general expansion with δ=c² and B=2c²+1. This proves a uniform eventual error bound for these trials without asserting any unproved numerical bound on Q or c. The constants for trials and minimizers may differ; denote them L and K respectively.

## The two comparison inequalities

For a minimizing triple write x_n=a_n/√n, y_n=d_n/√n, q_n=x_n²+y_n². Its actual objective is at most the admissible trial's objective. Combining the two absolute error bounds gives, with C=K+L,

F(q_n)≤F(2u_n²)+e_n[G(u_n,u_n)-G(x_n,y_n)]+C/n. (1)

For every q>0 there is the EXACT radial-excess identity

F(q)-F(q_0)=(q-q_0)²/(2q)≥0.

Subtract F(q_0) in the objective comparison, use the trial radial cost, and discard this nonnegative excess. Multiplying by √n then gives

G(x_n,y_n)≤G(u_n,u_n)+(16+C)/√n. (2)

These inequalities hold eventually for EVERY eventually minimizing choice. In particular (2) does not assume a convergence rate for q_n or balance of the chosen minimizer. comparison_algebra proves the exact algebra; minimizer_eventual_comparison supplies all hypotheses from the actual objective.

## Arbitrary clusters, including the axes

Take any convergent subsequence (x_n,y_n)→(x,y), with its indices tending to infinity. The common annulus gives x,y≥0 and x²+y²≥1/1024. The rational functions F and G are therefore continuous at this limit. In (1), e_n→0 and C/n→0, so F(x²+y²)≤F(q_0). The exact excess identity forces x²+y²=q_0. In (2), continuity gives G(x,y)≤G(c,c).

Since c^4=Q, at radius q_0=2c² the coefficient -1/2+2Q/q_0² is zero, and

G(x,y)=(c²+1)(x³+y³)/(2c²).

For nonnegative x,y on this radius, strict convexity of t↦t^(3/2) implies x³+y³≥2c³, with equality only at x=y=c. Equivalently the checked angular_cubic theorem gives this inequality and its equality condition directly. Hence the G comparison forces (x,y)=(c,c), including exclusion of axis limits. minimizing_cluster_balanced formalizes this for arbitrary cofinal subsequences, not a specially selected balanced minimizer.

## Full convergence and the path limit

All sufficiently late pairs lie in [0,32]². If the full sequence failed to tend to (c,c), some ε>0 would have infinitely many pairs at distance at least ε. The intersection of this closed complement of the ε-ball with [0,32]² is compact. It supplies a convergent subsequence whose limit remains at distance at least ε, contradicting the cluster conclusion. Thus the full pair converges. In particular q_n→q_0; this is obtained from the exact radial identity and compactness, with no assumed rate.

Finally the exact identity a_n+b_n+d_n=n implies, eventually,

b_n/n = 1-(x_n+y_n)/√n → 1.

This proves all three asserted limits. The formal source_target theorem has precisely the universal eventual-minimizer hypothesis in the statement and no unpaid bridges. minimum_attained establishes existence for each n≥3.

## Formal certificate and limits of this implementation

SOURCE-APPENDIX-v4.md contains every literal local production source, including all 48 cached dependency sources and seven new modules (55 total). SOURCE-MAP-v4.json maps each source, imports, source/olean hashes and documentary cache origins. PINS.json identifies the read-only toolchain and standard libraries. Twenty-six new calls were made, including twelve retained failures; all seven new production modules were compiled and separately kernel checked. AuditV4 supplies the fully expanded endpoint and transitive critical axiom audits, allowing only propext, Classical.choice, Quot.sound. There are no added axioms, sorry/admit, unsafe, native_decide or oracle in the successful production proof. Failed versions and their diagnostics are retained separately.

This run reused the 48 explicitly granted checked dependencies. It is NOT a fresh build of all 55 modules and NOT an independent extracted replay. Future independent acceptance MUST commission a NEW task to extract, freshly compile and separately kernel-check the ENTIRE source closure without these campaign oleans. Current source/binding/substantiality/104-distinctness/dated373-registry qualifications are inherited to their recorded scope; the new 105th pure-flag comparison remains for independent acceptance. All inherited and current process failures are unwaived. Formal closure alone is not an acceptance or novelty decision. No credit, ledger, registry, publication or count action is taken here.

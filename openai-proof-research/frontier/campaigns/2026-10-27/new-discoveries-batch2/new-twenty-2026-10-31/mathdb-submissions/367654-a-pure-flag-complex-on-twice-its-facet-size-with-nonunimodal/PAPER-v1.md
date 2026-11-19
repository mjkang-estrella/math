# A counterexample to the literal broad pure-flag unimodality assertion

Implementation certificate v1, 2026-11-15 UTC. Target MathDB367654, formal pass r3. This is a mathematical proof and Lean implementation report, not a novelty, acceptance, publication or independent-replay claim.

## Statement and binding

The assertion refuted here says that every finite abstract pure flag complex of dimension d−1 on exactly 2d actual vertices has unimodal dimension-indexed f-vector (f₀,…,f_{d−1}). Empty faces are not coordinates of that vector. “Pure” means that a facet exists and every inclusion-maximal face has d vertices; “flag” means that every set whose pairs are faces is a face. Every singleton must be a face. Unimodal means weakly increasing up to some index m<d and weakly decreasing afterwards.

The owned certificate plan and inherited fidelity review bind this literal broad assertion to arXiv:2503.18490v1, *Spheres and balls as independence complexes*, 24 March 2025, p.2, Conjecture 1.4, and MathDB367654. This pass did not independently extract or reread the PDF, retrieve a current registry, or examine the later journal final. Source binding and prior qualification against 103 families are inherited; subsequent independent acceptance must include 104 scopes. The journal-final route remains closed under the work-specific controls. No equivalence with that final version is claimed. The original ISOLATE-FREE GRAPH CONJECTURE remains UNREFUTED: our graph deliberately has isolated vertices.

The formal endpoint is PureFlag.literal_broad_refutation in FinalWitness.lean. It proves ¬allTypesBroadConjecture, whose universal ranges over finite vertex types V:Type, decidable equality, and FiniteComplex V. An explicit finite witness in this universe already disproves the ordinary unrestricted assertion. No graph-class hypothesis is silently removed from an isolate-free conjecture.

## Construction on actual vertices

Fix a positive natural a. Let A be the disjoint union of a copies of K₁ and a copies of K₅. Let B be the disjoint union of a copies of K₂ and a copies of K₃. Form their complete join, so that every vertex of A is adjacent to every vertex of B, and add an independent disjoint set E of 7a isolated vertices. Vertices are tagged finite types, not a nominal count: ((Fin a×Fin1)+(Fin a×Fin5))+((Fin a×Fin2)+(Fin a×Fin3)), followed by the disjoint summand Fin(7a), with the parenthesization fixed by Vertices. Thus the graph has (1+5+2+3+7)a=18a actual vertices.

Let Δ be its independence complex. Independence is downward closed, includes the empty set and all singletons, and is determined by pairs, hence Δ is flag. A maximal independent set contains E. Its remaining part lies in one branch, since cross edges forbid using both. Within that branch it must choose exactly one vertex from each of its 2a cliques: a missing clique permits an additional vertex. Conversely, any such full choice is nonempty when a>0 and blocks the opposite branch, so it gives a maximal set after adding E. Consequently every facet has 2a+7a=9a vertices, and a facet exists by explicitly selecting one vertex in every A clique and adding E. Therefore Δ is pure of dimension 9a−1. This is proved for actual finite subsets by graph_facet_card and graph_pure, not inferred from the polynomial.

## Actual face counts

Let F(x) count independent subsets by cardinality, including the empty set. Restriction to disjoint components gives size-preserving face bijections; the complete join gives a choice of branch, with only the empty face counted twice. A clique of size b contributes 1+bx, and t isolated vertices contribute (1+x)^t. These bijections give

F=(1+x)^{7a}[((1+x)(1+5x))^a+((1+2x)(1+3x))^a−1]
 =F₁+F₂−F₀,

where F₁=(1+x)^{8a}(1+5x)^a, F₂=(1+x)^{7a}(1+2x)^a(1+3x)^a, and F₀=(1+x)^{7a}.

The coefficient c_j counts actual independent j-subsets, so c_j≥0, c_j=0 for j>9a, and f_i=c_{i+1}. FaceBijections, FacePolynomial, GraphPolynomial and FTransport establish those equalities without replacing Δ by a surrogate polynomial. Integer coefficients are transported to rationals by actualRat; the map is coefficient-preserving.

## Symbolic normalization and moments

Set M=2^{7a}12^a>0, S=2^{7a}, q=S/M=12^{−a}. For a≥1, 12^a≥12, so 0<q≤1/12. A normalized Bernoulli polynomial is β_b=(1+bx)/(1+b). Its mass is 1, its mean b/(1+b), and its centered variance b/(1+b)^2. Finite product sums show that masses multiply and means and variances add for normalized independent factors. This follows by expanding the first and second moments and using finite distributivity; no probabilistic limit theorem is used.

The checked trial construction takes finite tuples of Bool choices, multiplies their rational weights, and pushes the weights forward by the number of chosen entries. Its degree polynomial is exactly β_b^n. Degree transport, rather than coefficient enumeration, identifies mass, first moment and second moment with the corresponding coefficient sums.

For F₁/M the normalized polynomial is β₁^{8a}β₅^a. Its mean is 8a/2+5a/6=29a/6 and variance 8a/4+5a/36=77a/36. For F₂/M it is β₁^{7a}β₂^aβ₃^a, with mean 7a/2+2a/3+3a/4=59a/12 and variance 7a/4+2a/9+3a/16=311a/144. The common masses agree because 2^{8a}6^a=2^{7a}12^a=2^{7a}3^a4^a. F₀/S has normalized polynomial β₁^{7a} and mass 1.

BranchScaling proves these exact scaling identities; ActualNormalization connects them to F, coefficient by coefficient. RangeMoments proves that trial degrees are at most their number of trials and extends sums to 0≤j≤9a using zero coefficients off the pushforward support. Thus no tail is silently truncated. ActualDistribution proves the raw branch totals really equal M. For w_j=c_j/M one has

w_j=p₁(j)+p₂(j)−q p₀(j),  w_j≥0,  ∑_{j=0}^{9a}w_j=2−q.

Here p₁,p₂,p₀ are the three normalized coefficient sequences, each with mass 1 on that full range. The nonnegativity of the signed combination comes from actual graph counts.

## Three exact finite windows

Take a=30000 and d=270000. The branch means are μ₁=145000 and μ₂=147500; variances are v₁=192500/3 and v₂=194375/3. Put r=625 and use consecutive half-open integer blocks

I₁=[144375,145625), I₂=[145625,146875), I₃=[146875,148125).

Every block has 1250 entries. Every index is positive and at most d. For a nonnegative mass-one finite sequence p, summing r²p_j≤(j−μ)²p_j over any subset where |j−μ|≥r gives outside mass ≤v/r². This is finite_chebyshev. Outside I₁, the distance from μ₁ is at least r; outside I₃, the distance from μ₂ is at least r. Consequently

∑_{I₁}p₁≥1−308/1875,   ∑_{I₃}p₂≥1−311/1875.

Each p₀ block mass is at most its full mass 1, and the other positive branch can be discarded in a lower bound. Writing b_k=∑_{I_k}w_j therefore gives

b₁≥1−308/1875−q,   b₃≥1−311/1875−q.

The blocks are pairwise disjoint subsets of the full support range. Nonnegativity on its complement, including j=0, yields b₂≤(2−q)−b₁−b₃. No assertion that positive-index mass alone equals 2−q is used.

Small rational arithmetic now gives

b₁−(2−q)/3≥1277/11250>0,
b₃−(2−q)/3≥1259/11250>0.

Hence b₂<(2−q)/3 and b₂<b₁,b₃. ActualBlocks proves this strict three-block valley. All powers remain symbolic. The equality a=30000 is discharged by reflexivity at the endpoint; it is not an outstanding hypothesis. This symbolic staging also avoids eager kernel reduction of large powers seen in preserved failed concrete drafts.

## Why these blocks obstruct unimodality

Extend the finite list f₀,…,f_{d−1} by zero to integer indices. A unimodal nonnegative list gives an extended sequence u with a global mode m. For H(s)=∑_{i=0}^{L−1}u(s+i), its first difference is H(s+1)−H(s)=u(s+L)−u(s).

A negative difference at s forces m<s+L; a positive difference at a later t forces t<m. These imply s<t<m<s+L<t+L. Monotonicity on either side of m then gives u(s)≤u(t) and u(t+L)≤u(s+L), contradicting the two strict difference signs. A valley H(s)>H(s+L)<H(s+2L) supplies such a negative difference followed by a positive one by finite telescoping. Therefore sliding block sums of a unimodal sequence cannot have this valley.

Our f-index shift is j=i+1. The three f-window starts are 144374,145624,146874, with L=1250. block_window proves their sums divided by M equal b₁,b₂,b₃, by a finite index bijection and actual_f_coeff. It checks j≥1 and j≤9a before invoking zero-extension translation. Since M>0, the strict valley transfers to the f-window sums. finite_window_valley contradicts unimodality. Thus graphComplex30000 is flag and pure with facet size270000, has540000 actual vertices, and has nonunimodal actual f-vector.

## Certificate status and limits

FinalWitness proves actual_f_not_unimodal, actual_missing_witness and literal_broad_refutation. Every new production module compiles with warnings treated as errors and passes a separate leanchecker invocation. AuditV3 transitively audits35 critical declarations, including graph/count/moment/window/transport/universal-negation roots; only propext, Classical.choice and Quot.sound occur. The endpoint has exactly those three axioms. No sorry/admit/new axiom/unsafe/native_decide or numerical oracle is used in production.

The complete local source closure, hashes, commands, pins, failed drafts, resource receipts and process deviations accompany this paper. This pass used60/72 formal calls, including18 failed compiles, and performed no independent extracted replay. All inherited process defects and new read/display defects remain UNWAIVED. Original source qualification, novelty/significance, independent statement fidelity,104-scope comparison, clean extracted replay and acceptance are separate gates. Zero credit is added by this worker.

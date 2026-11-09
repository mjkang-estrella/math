# Sustained mathematics and exact residual scopes

No new literal source question was completely resolved. This file preserves successful identities, failed transfers and the remaining quantifiers; none is offered for counting.

## Ternary exact-cardinality question: route A, complete finite deletion DAG

Grytczuk–Stankiewicz2011.12822v1 Problem1 asks for one word over {a,b,c} with exactly80 square-free reducts. Let C(w) be the SET of distinct words obtained by one deletion UXXV->UXV, X nonempty. Define

R(w)={w} if C(w) is empty, and R(w)=union_(u in C(w)) R(u) otherwise.

This is an exact recursion, not a heuristic interpretation of reduct: every edge decreases length, so induction on |w| proves both inclusions. If C(w) is empty w is square-free. Otherwise every complete reduction starts with one element of C(w), and every terminal reduction of any such child is a terminal reduction of w. Different paths reaching the same terminal word are counted ONCE.

`checks.py` implements the recursion by postorder processing and sets of terminal words. The source's word

`abcbabcbcacbcacabacabcbacabcabacacbcacbabcbcacbca`

has length49, exactly2928 reachable words and exactly81 terminals. An independently written breadth-first closure deletes the SECOND copy of each square; its terminal set equals the postorder implementation's complete81-element set (`independent-check.json`). Deleting either of two equal adjacent blocks yields the same resulting word, so this algorithmic difference is valid. This is a reproducibility check of an existing source example, not a new theorem.

Local insertions, deletions, substitutions and short duplications around that word were tested with seed250, a125-second internal wall stop and a40000-state per-candidate stop. The completed run evaluated163 trials, with counts14 through100 and minimum distance1 from80. No80 was found. It does NOT certify all one-edit neighbors, all words through a fixed length, or absence of80 over unbounded length. The source's reported missing cardinality therefore remains entirely unresolved here. The state's complete terminal sets support exact statements only about the particular processed words.

The decisive constructive improvement would be a small parametrized word grammar whose reduct DAG can be classified symbolically, rather than another repetition of this local sweep.

## Route B, separator product and failure to transfer four letters to three

Here is a full elementary composition lemma. If # is absent from finite words u and v, then

R(u#v)={p#q : p in R(u), q in R(v)}.

Proof: any square crossing the unique # would contain # once, whereas a square contains an even number of occurrences of each letter. Thus every reduction lies wholly on one side. The unique # persists, so the same argument applies after every reduction. Terminality is exactly terminality on both sides; all pairs of terminating reductions can be interleaved. Equality and the product cardinality |R(u#v)|=|R(u)||R(v)| follow, since # gives a unique parsing of the output. A square cannot merely straddle # without containing it because squares are contiguous factors.

This suggests80=5*16. But taking ternary u,v and a fresh # uses FOUR letters. If # is one of the three allowed letters and is absent on both sides, both sides are binary. Actual source Proposition1 proves every nonempty binary word has exactly one reduct by preservation of initial/final letters and the six binary square-free words. Empty sides also have one reduct. Thus this unique-separator scheme produces ONE, never80, in the ternary case. This is a rigorous obstruction to this construction route, not an obstruction to Problem1.

The actual source Theorem3 constructs every cardinality over four letters by a different additive prefix/gadget construction, with F=xabaxababx and a fourth-letter square-free context. Its proof pp5–7 was read. Merely identifying two of its four letters is invalid: it can create new squares, merge previously distinct terminal words and destroy terminality. An encoding into ternary words would need BOTH preservation and an exact description of every new reduction crossing a code boundary. Square-free preservation by itself does not provide that inverse bridge. No such reduction-reflecting code is established. This is the second genuine construction route, with the exact missing step exposed.

Residual question: exists W in {a,b,c}* such that |R(W)|=80? No upper bound on |W| is imposed. Conjecture1 (infinitely many missing values) and Conjecture3 (one-step outdegree<=length) are not answered by the calculations above.

## The connected-component conjecture is a free-band adaptation, zero credit

The source's Conjecture4 asks whether the undirected square-reduction/duplication graph on all k-letter words has finitely many components for every finite k>=2. Its equivalence relation is exactly the least semigroup congruence containing (X²,X) for every nonempty word X: every elementary move is an application of such a relation in a left/right context, and a finite congruence derivation is a path of those moves. Thus the nonempty-word components are the elements of the free band on k generators. If the empty word is included, it adds one isolated component.

Actual Cirpons–Mitchell2209.05334v3 pp1–2 explicitly defines that quotient and states local finiteness; its Table1.1 lists sizes1,6,159,332380 for k1..4. This is an exact full-scope classical subsumption, not a new conjecture resolution. Its complete rewriting system (2)–(3) uses X²->X and xyz->xz when cont(y) is contained in cont(x)=cont(z). The modern paper attributes the underlying finiteness theorem to earlier band theory; those oldest bodies were not independently retrieved. Public2022/2023 text already suffices to exclude discovery credit in2026. Finiteness of components does not bound the number of directed square-free terminals in an individual component; infinite irreducible representatives can coexist in one component. It does not solve the80 question.

## Graph normalization: two universal routes, already publicly proved

Set B=A+I for a finite simple graph and take x_i>0. Write d_i=(Bx)_i and y_i=x_i/d_i. Direct expansion and symmetry give the identity

sum_i y_i - y^T B y = (1/2) sum_(i,j) B_ij x_i x_j (1/d_i-1/d_j)^2 >=0.

Indeed the two diagonal-square terms each sum to sum_i x_i/d_i because sum_j B_ij x_j=d_i; the cross term is y^TBy. On a connected graph equality means d_i constant along every edge, hence d=c*1. Then By=Bx/c=1, so y is fixed by normalization. The INITIAL x need not be fixed: any nonunit rescaling of a fixed point has the same normalized image. This avoids silently inheriting the source's imprecise strictness wording.

A second route uses reversibility. Let P_ij=B_ij x_j/d_i, pi_i=x_i d_i and f_i=1/d_i. Row sums of P are1 and pi_i P_ij=B_ij x_i x_j=pi_j P_ji. Jensen gives sum_i pi_i(Pf)_i²<=sum_i pi_i f_i²; alternatively the Dirichlet form directly gives <f,(I-P)f>_pi>=0. Here ||f||_pi²=sum y and <f,Pf>_pi=y^TBy, proving the same literal inequality. This is a general symmetric-nonnegative-matrix fact, not dependent on spectral positivity of B.

These proofs completely adapt to Guigues2020 Conjecture8.1. But Guigues2605.05330v1 AppendixF Lemma1, with S=B,v=1,z=x, already gives the exact inequality and edge-square proof, including equality in the normalized image. Therefore zero discovery credit, regardless of proof size. The later paper's Theorem2, AppendixB and AppendixE were body-read: energy majorization and a Kurdyka–Lojasiewicz relative-error argument are explicitly presented for broader weighted dynamics. This report does not certify that whole argument at boundary coordinates. No attempt to repackage that public convergence claim as a fresh result is made.

## Monomial domination: obstruction to the first universal exchange route

In G_n(d), write a neighbor of exponent vector v as v-e_j+e_i. When min(n,d)<=2 the source's Proposition4.5 makes the graph claw-free, so its cited Allan–Laskar theorem gives gamma=i. For n,d>=3 the source explicitly constructs an induced claw. Consequently a proof that works for every induced subgraph by claw-free exchanges is impossible; the actual graph need not be domination-perfect (source Figure5 exhibits this already in G3(4)). This does not refute equality for the whole graph.

An alternative finite route optimized domination and independent domination separately. The ten pairs (3,d),3<=d<=8; (4,d),3<=d<=5; and(5,3) gave equal reported optima3,3,5,6,7,9,4,6,8,5. `monomial-diagnostics.json` retains selected exponent vectors. Each selected set is checked using integer-rounded membership and the exact0/1 closed-neighborhood constraints, plus pairwise nonadjacency for the independent witness. Floating solver lower bounds are diagnostics only; no exact lower certificate or universal equality follows. A future counterexample would need a rigorously certified lower bound for i exceeding an explicit dominating-set size, not a floating discrepancy. The full all-n,d exchange argument remains missing.

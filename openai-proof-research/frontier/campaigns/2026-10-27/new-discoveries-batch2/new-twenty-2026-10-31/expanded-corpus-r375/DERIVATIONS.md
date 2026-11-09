# R375 ordinary mathematical dossier — zero credit

This dossier reads the fixed literal records in raw-provenance.json. It does not certify novelty, formal correctness or acceptance. Source read ranges are identified below; acquisition of a PDF is not full semantic reading. No enumeration, numerical diagnostics, formal tools or children were used.

## 323739: complete finite-source multispin independence bridge

Source: Bernardi, arXiv:1207.0896v3. Actual definitions in introduction and final Conjecture 9; section 4, equation (12), Laplacian and directed weighted forest identity, and its product-matrix argument were read. The author-hosted companion PDF failed certificate verification and was not retried. Latest arXiv metadata reports v3, 12 July 2012; the PDF internally bears an October 2018 date. These dates are recorded separately and are not proof of publication priority.

Let U be the finite base vertex set, |U|=d, and p>=1. A rooted directed forest has one outgoing arc at each nonroot, no directed cycles, and all arcs lead to the unique chosen root of a component. This is exactly the source convention. Loops, if allowed in a base representation, cannot occur in forests and are omitted from the Laplacian. Parallel arcs may be given separate indeterminates. To implement the uniform conditional distribution, give every base arc a an independent marker x_a (set any fixed background weights to 1); each horizontal lift has that same marker. Give the vertical arc (u,i)->(u,j), i!=j, marker y_{u,j}. Put Y_u=sum_j y_{u,j}. The multispin at u is precisely the exponent vector of its y variables, not the entire local subforest.

Over the rational function field in these indeterminates, write L for the base row Laplacian: diagonal outgoing-weight sum and off-diagonal minus outgoing weight. Acting on functions f(u,i), the full Laplacian is

 (L_H f)(u,i) = sum_{a:u->v} x_a(f(u,i)-f(v,i))
                 +Y_u f(u,i)-sum_j y_{u,j}f(u,j).

The j=i term cancels, so this formula includes no vertical loops. The subspace C of functions constant on each fibre is invariant. On C the vertical part is zero and L_H acts as L. Identify the quotient with Q^U tensor (Q^p/<1>). The final summation term has image in C even when the y variables depend on u, and hence vanishes in the quotient. The induced quotient operator is (L+diag(Y_u)) tensor I_{p-1}. Choose any basis of C extended to a basis of all functions. The matrix is block triangular. Therefore, including the root marker t, the source's directed weighted matrix-tree/forest identity gives the polynomial identity

 F_H(t;x,y) = det(t I_d+L) det(t I_d+L+diag(Y_u))^(p-1).       (A)

No spectral genericity, diagonalizability, connectedness or positivity is needed. Proving this in the rational function field proves it as an integer polynomial identity by injectivity of the polynomial ring into its fraction field. For p=1 the quotient is zero dimensional and its determinant contribution is 1. Empty base is vacuous.

Fix the exact G-projection of F0: horizontal multiplicities h_a and vertical counts k_u. It has positive fibre size by existence of F0. In (A), after extraction of x^h and multidegree k in each y-group and after t=1, dependence only on Y means that the conditional enumerator is

 c_h,k product_u (sum_j y_{u,j})^k_u.

To justify this without an independence assumption: expand the right side as a polynomial in the independent formal symbols Y_u; substitution Y_u=sum_j y_u,j preserves degree in each group. The prescribed group degrees select exactly the single monomial product Y_u^k_u. The coefficient c_h,k is positive: specialize all y to 1; the result counts the nonempty projection fibre and equals c_h,k p^(sum k_u). The apparent coefficient is an integer since it is the coefficient of product y_{u,1}^k_u in the forest enumerator. The number of roots is already forced by dp-sum h-sum k, so setting t=1 loses no condition.

Thus for every collection of nonnegative spin multiplicities m_u,j with sum_j m_u,j=k_u,

 Pr(all sigma_u=m_u) = product_u [ k_u!/(product_j m_u,j!) p^(-k_u) ].

If any total is wrong the probability is zero. Summing over all other groups gives the corresponding marginal; hence these probabilities factor into all marginals. This proves the exact finite-source Conjecture 9, even the stated multinomial law. Weighted conditional sampling also follows when the weight is constant on the projection fibre; arbitrary extra spin-dependent reweighting is a different question.

Failed shortcut and repair: Proposition 6 alone only treats identical vertical weights across all fibres, which cannot distinguish sigma_u. That global specialization alone does not prove independence. The invariant-subspace argument above repairs precisely this local-variable gap. A proposed coupling of entire vertical subforests would prove a stronger statement expressly reported false in the source; it is neither needed nor claimed. Conditioning fixes multiplicities, not horizontal edge positions.

Disposition: complete ordinary finite-source reduction to the source's equation (12) and explicit block-triangular linear algebra. Treat as routine classical/source bridge, zero credit under the task standard; not excluded because it is short or familiar. Infinite-base uniform probability is not defined by the record and no infinite extension is claimed. Original explicit endpoint priority, journal/correction clearance and independent review remain unproved. No Pi authorization or certificate plan for credit.

## 323464: literal refutation, authenticated omitted-domain correction

Initial actual arXiv:1205.0513v1 definitions 2.1/2.2, finite theorem 2.4 and its proof, and Conjecture 2.12 were read. Closed neighborhoods include the vertex itself. A clique is nonempty; an infinite clique would also be a clique under that definition. Infinite dismantlability here means that each finite vertex set lies in a finite induced dismantlable graph, not a global well-founded dismantling order.

Let V=N x {0,1}. Join (n,e) to (m,f) iff n!=m. This is a simple undirected graph. Let s(n,e)=(n,1-e), and H={id,s}; s^2=id, s is nontrivial and preserves adjacency, so H is a finite subgroup of automorphisms of order 2.

For any finite A subset V, choose n outside the finite set of its first coordinates and put z=(n,0). The finite induced graph on S=A union {z} is a cone with apex z. Its closed neighborhood at z is S. List the elements of A in any order, followed by z. At each deletion stage every remaining other vertex has its closed neighborhood contained in that of z; thus each is dominated by z. This explicitly supplies a dismantling order for every A, including empty A. Hence this infinite graph satisfies the literal hypothesis.

If K were a nonempty H-invariant clique, choose (n,e) in K. Invariance puts (n,1-e) in K. These are distinct and nonadjacent, contradicting the clique condition. This rules out finite and infinite invariant cliques. Meanwhile {(n,0):n in N} is an infinite clique.

Two mechanisms checked: (i) an arbitrary finite dismantlable hull S cannot simply be saturated to HS and then fed to the finite theorem; in this example any nonempty H-invariant finite set consists of whole opposite pairs and has no dominated vertices (for each candidate dominating vertex a nonneighbor witnesses failure). (ii) iteration of hull and saturation yields an exhaustion, but cannot supply a terminal H-invariant finite dismantlable stage or a fixed clique in the limit. The explicit graph resolves the missing-infinite-clique escape, not the corrected question.

Crucial primary companion: https://www.math.uni.wroc.pl/~dosaj/trav/rd-web.pdf, actual Conjecture 2.11 at extracted lines 384–389, adds the hypothesis of no infinite cliques and explicitly credits Dawid Kielak for necessity. This is actual text, not the abstract's stronger-sounding summary. Its timestamp is not authenticated; arXiv's only listed version is v1 in May 2012 and its metadata cites the 2014 journal. The precise date this correction entered is not established here. The explicit construction above pays every bridge from the omission to a literal counterexample. It violates the added hypothesis, so it gives no counterexample to the revised conjecture. Zero-credit domain correction; no Pi. Polat's specific infinite-graph theorem remains unread and is not invoked as a general subsumer.

## 323948: known primitive sigma-LFSR formula, complete counting reduction

Ram's current arXiv:1208.2500 actual introduction prints Conjecture 1.1 and then explicitly says Chen–Tseng's splitting-subspace theorem settles it. The body concerns restricted TSRs elsewhere: do not confuse sigma-LFSRs with that narrower family. The record's c3 is corrupted sigma notation. Chen–Tseng arXiv:1208.0851v2 actual splitting definition, Corollary 3.4 and substitution proof were read; theorem 3.3 and portions of its recursion proof were acquired/excerpted, not independently audited in full. Metadata authenticates August 25, 2012 v2 and a corrected (1-q) factor in the L=R computation; journal metadata is Finite Fields Appl.24 (2013),15–28. Final journal proof and further corrections remain unread.

Here is the full transport from that theorem, not a claim to reprove its recursion. Put D=mn, fix a primitive element alpha of F_{q^D}, and let T be multiplication by alpha. The theorem says the number of m-dimensional W with direct sum W+alpha W+...+alpha^(n-1)W=F_{q^D} is

 S=(q^D-1)/(q^m-1) q^[m(m-1)(n-1)].

Each W has |GL_m(q)| ordered bases v_1,...,v_m. For each such basis form the ordered field basis (v_1,...,v_m,alpha v_1,...,alpha v_m,...,alpha^(n-1)v_m). In that basis T has the shift block-companion shape, with arbitrary m by m feedback blocks, exactly a sigma-LFSR state matrix (transpose conventions biject the same objects). Conversely every block companion with characteristic polynomial the minimal polynomial f of alpha is conjugate to T, and an intertwining field-basis is of this form: its later blocks are forced by multiplication from the first block. The first block spans a splitting subspace. Thus all matrices in the fixed f fibre occur.

Two such ordered splitting bases give the same state matrix iff their change-of-basis centralizes T. Every commuting linear map is multiplication by c in F_{q^D}: its value on 1 determines it since 1,alpha,...,alpha^(D-1) span. It is invertible iff c!=0. This action on bases is free and has q^D-1 elements per orbit. The fixed-polynomial fibre therefore has

 S |GL_m(q)|/(q^D-1) = q^[m(m-1)(n-1)] product_{i=1}^{m-1}(q^m-q^i)

matrices, using |GL_m(q)|=product_{i=0}^{m-1}(q^m-q^i). There are phi(q^D-1)/D primitive monic degree-D polynomials: primitive elements have Frobenius orbits of exactly D, because a proper subfield cannot contain an element of order q^D-1. Multiplying yields exactly the displayed record formula, for all positive m,n and prime powers q. Empty products include m=1; n=1 gives the Singer-cycle count without exception.

For semantic completeness, multiplication by a primitive alpha gives every nonzero state period q^D-1. Conversely a transition with every nonzero vector of that period is invertible and has no proper nonzero invariant subspace, since such a subspace has fewer than q^D-1 nonzero vectors. Its module over F_q[X] is therefore simple, its characteristic polynomial irreducible degree D, and its field multiplier has order q^D-1. This gives the exact primitive-LFSR criterion rather than just a matrix count.

The earlier shortcut 'count primitive polynomials' misses an entire fibre. Counting all ordered field bases overcounts and includes nonsplitting first blocks. The splitting theorem and centralizer quotient pay both gaps. Zero credit: actual source reports resolution, with complete source-to-record reduction above. No claim of a new theorem or a new first proof.

## Other focused failures

323905: actual hatted definition differs from barred definition by allowing the inserted entry to take any pattern role. A proof for ordinary pattern avoidance, or the source's factorial inflation in its bond subcase, does not cover all hats. Proposition 3 equates hatted and barred avoidance only under its nonbond hypothesis; it is not itself an exponential enumeration theorem. Conjecture 1 remains stated in the actual source, so the record's 'refuted according to source' note cannot be applied blindly. No independent full refutation or full-scope construction was obtained. HOLD; no exclusion by familiarity.

354348: actual source Conjecture 13 read, together with Theorems 1,2,3,4,7 and stated proof obstruction. Four-translate control does not follow by summing two three-translate bounds: the uncontrolled fourth translate can add order n points. Endpoint averaging at min B and max B proves a lower bound and the epsilon=0 equality case, but the source's two-block random-density model shows that particular averaging strategy does not establish stability for arbitrary epsilon. No random instance was computed. Exact gap: a uniform mechanism using all triples to force A close to one progression and B contained in a progression of matching step, with both errors <=delta n. Four-translates theorem and exact equality case are helpers, not the endpoint. HOLD.

323942: source Definition 4 uses contextual outcome equality; Conjecture 21 concerns a different equivalence symbol and a restricted negative-score universe. Therefore substituting 'equality implies isomorphism' from ordinary algebra, or transferring the positive-score Theorem 13, does not pay the contextual quantifier. Selected definitions and theorem/conjecture passages read; game-tree Figure8 not visually verified. HOLD both semantic and proof gates.

323073: the reference's Green/Sapozhenko solved note concerns Cameron–Erdos, not automatically this distinct counting estimate. A small-doubling structural containment bound cannot be summed over all progression parameters without controlling their contribution by 2^(delta m). The m>=C log n condition suggests absorption of polynomial n factors only; it does not pay the shape-counting theorem for the full m>=C sqrt N range. Actual source acquired and selected conjecture passages read. HOLD; no solved label inferred from the unrelated note.

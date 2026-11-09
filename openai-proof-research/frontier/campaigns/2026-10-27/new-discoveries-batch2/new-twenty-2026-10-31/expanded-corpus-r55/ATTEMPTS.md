# Sustained routes and qualification limits

## 361086 dense Kneser minimizer

Primary Section 1 definitions, Conjecture 2.5 and surrounding Example 2.6 read, including the distinction between minimizing edges and maximum degree. The primary conjecture page was rendered and visually checked. The solver model selects k-subsets and enforces the conditional maximum-degree bound by big-M equal to the full Kneser degree. It found n=7,k=2,m=11 after three smaller cases. This is only a search diagnostic. An independent exact Python enumeration reproduced the gap on all 1365 compressed families. The final ordinary proof is in KNESER-PROOF.md.

A first handshaking shortcut only yielded a degree sum <=8, giving four disjoint neighbours, not five. This off-by-one was caught during proof write-up. The completed argument separates complement maximum degree >=3 from maximum degree <=2 and handles the latter by its degree-2 vertices. The final proof does not rely on the solver or enumeration.

The nearest predecessor Frankl–Kupavskii arXiv:2004.08718v1 definitions, Theorems 5–7, and proof of Theorem 6 were read. These concern large k and n>=16t²k² / 64k² and do not directly supply this small exact counterexample; the whole predecessor was not read. Journal DOI10.5070/C65165027 was identified, but the journal PDF returned 403 and the landing page challenged the web fetch. No retries or bypass were attempted. Qualification remains HOLD and formalization was deferred per the source-gap instruction. No exhaustive prior-art or novelty claim.

## 360899 / 360900 unrestricted trapezoids

Read Definitions 1–3, Conjectures 1–3, Proposition 4 proof, Theorem 4 proof, and the stated Favard-length input in Kuklinski arXiv:2311.16210v1. Recovered literal parallelogram slices [(k-1+(j-k)y)/n,(k+(j-k)y)/n]. The prose describing the endpoints in the PDF swaps j,k compared with this inequality; inversion of a permutation leaves the minimum unchanged. Used the inequalities themselves in the script.

Exact rational integration subdivides y in [0,1] at every intersection of interval endpoints, sorts the intervals and integrates the piecewise linear union length by trapezoids. All permutations through n=7 were evaluated. Minima:1,3/4,2/3,5/8,3/5,7/12,4/7. Reversal attains them. This proves nothing about later minima or monotonicity until the integration/enumeration semantics are formally certified.

Beyond the sweep: subdividing each strip of a permutation into q equal parallel strips gives the same measurable union, so alpha(qn)<=alpha(n). Appending an identity block yields only alpha(n+1)<=(n alpha(n)+1)/(n+1), which does not establish consecutive monotonicity. A hoped-for deletion/compression induction fails because deleting a strip changes overlaps of the others. The logarithmic conjecture requires exponent1 in log n; the source's Favard-based positive exponent p is not enough. No bridge removing this exponent gap was found. Park both claims. No endpoint/domain correction credit for n=1 and log1.

## 361574 Chebyshev hyperplanes

Read Chebyshev Varieties Theorem 3.9, Lemmas3.10–3.11 and their proof bodies, Corollary 3.12 proof, Example 3.13 and Conjecture 6.1. The polynomial left inverse P proves the parametrization injective and its image closed; real parameters give distinct real curve points. This supplies the semantic bridge that merely counting polynomial roots would omit.

Routine full-scope argument: set a=min a_j and q(t)=sum c_j T_{a_j}(t). If q=0 identically, the hyperplane contains the whole curve. Otherwise q is orthogonal, for positive Chebyshev weight(1-t²)^(-1/2) on(-1,1), to every polynomial of degree<a. If q had fewer than a sign-changing zeros there, form p as the product of its sign-changing linear factors, with sign chosen so pq>=0. Then degree p<a but integral pq against the weight is strictly positive, contradicting orthogonality. Hence q has at least a distinct real roots and Theorem 3.9 gives at least a distinct real curve points. For a=0 the bound is vacuous. Repeated exponents or cancellation simply keep q in the same orthogonal complement.

The classical Sturm–Hurwitz–Kellogg statement and Chebyshev-system definition were read in the primary introduction of arXiv:0710.5902; its actual main theorem proves a converse, not the forward classical theorem. Its forward theorem proof is not given there and the cited2005 book was not read. The elementary polynomial-product argument above independently fills the needed forward proof in this particular setting. This is a routine orthogonality consequence with an explicit same-paper embedding bridge, excluded for credit. No claim that the original authors or a successor published this particular corollary; the 2026 journal version was not inspected.

## 360853 crown subgraphs

Read source word-uniformity and representation-number definitions, distinction from permutation representation, Conjecture 1 and nearby conclusion. Two routes considered: append a crownH5,5 to a crown-free high-representation bipartite component, or build an explicit non3-representable crown-free graph. Neither supplied a small explicit witness with a certified representation lower bound. A counting route would require a sparse high-girth family with enough labelled graphs to outrun the number of bounded-uniform words, followed by a full disjoint-union representation bridge; no completed theorem is claimed.

Live search found Colbrook–Drysdale arXiv:2609.35842v1. Read Theorem 1.1, Corollary 1.2 with proof, Section 1.1, and the Section 6.2 reduction proof. This is a genuine public theorem bounding representation number by vertex count and settling fixed-order crown extremality. It does NOT by itself bound representation number in terms of the largest induced crown size, the exact MathDB claim here. Other proof sections and its Lean repository were not audited. This is relevant primary prior art, not a full-scope exclusion bridge for360853. Exact crown-subgraph question remains parked.

## Other primary reads

360848: source Conjecture 6.5 concerns Qd,Rd,Sd,Td only. Read Propositions 6.1–6.4 proofs and Example 6.6's explicit design matrix, polynomial and Groebner-basis account. Example 6.6 already refutes the broad MathDB paraphrase. No credit for repeating it; four-family conjecture not solved or widened.

361186: read exact F, Theorem 1.3, Proposition 4.1, Theorem 4.13 proof and Conjecture 4.16. When4p+q²<0, Fxx(p,q)=-4p>0 and Hessian determinant positive, so P is a local minimum, contrary to 'maximum'. This is a source sign/wording error already visible in its own Hessian computation; excluded rather than credited.

361166: read Conjecture 4.5 and Theorem 4.6 proof, including its dependency Lemma 4.3 statement and Theorem 3.4's statement and opening proof paragraphs (the whole latter proof was not reviewed). The theorem characterizes equality by EVERY optimal code being even-like and containing1; this alone does not prove uniqueness up to equivalence. Source conclusion calls the conjecture solved, but a literal uniqueness bridge is not asserted here. Park as primary-known-related-result, not a fresh solution.

361070: read the ending of the source Theorem 6 proof, Theorem 7 and its proof, Proposition 1 proof ending, Proposition 2 statement and Conjecture 1. The alternating-subspace reduction only supplies the n+2 obstruction. Extending it by one dimension requires control of directions whose supremum is0, not attained at infinity. No completed topological bridge; parked.

361269: read interval impropriety definition, Theorem 12 proof, Conjecture 13 and Proposition 14 proof. Existing insertion method gives ceil(Delta/3), not constant2. Simply reusing the parent edge's color fails when one endpoint already has that color twice. A two-color-local extension can also fail when endpoint available colors do not intersect or differ by 1. No global recoloring invariant supplied; parked.

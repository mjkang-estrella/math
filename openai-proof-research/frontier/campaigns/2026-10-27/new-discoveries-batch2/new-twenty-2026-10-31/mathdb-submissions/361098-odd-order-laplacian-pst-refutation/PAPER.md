# Odd-order graphs with Laplacian perfect state transfer

## Abstract
For each integer k ≥ 1 we construct a connected simple unweighted bipartite graph of order 36k²−1 with Laplacian perfect state transfer at time π/2. This refutes Conjecture 77 of Kirkland and Monterde, *Quantum walks on join graphs*, arXiv:2312.06906v1. A Lean certificate verifies the 35-vertex member and the literal negation of the conjecture. The infinite family is proved below on paper.

## Statement and conventions
In §12 of [Kirkland–Monterde](https://arxiv.org/abs/2312.06906), Conjecture 77 reads:

> If X is a simple connected unweighted graph on an odd number of vertices, then Laplacian perfect state transfer does not occur in X.

The following quotations from §2 use typeset mathematical notation in place of the PDF text extraction's glyph encoding:

> The Laplacian matrix of X is the matrix L(X) = D(X) − A(X).

> U_H(X,t) = e^{itH}.

> We say that perfect state transfer (PST) occurs between two vertices u and v if |U_M(X,τ)_{u,v}| = 1 for some time τ.

Here D is the diagonal matrix of vertex degrees, A is adjacency, and e_u is the characteristic vector of vertex u. We take M=L. All graphs below have no loops and each edge has weight one. Transfer is between distinct vertices at positive time. L is real symmetric, hence U_L(t) is symmetric and unitary. The source's (u,v) convention and our destination/source (v,u) convention agree by symmetry. The source defines PST by an entry, so no equivalence with a vector-based definition is needed for the formal endpoint. Changing the convention to exp(−itL) would not change PST: since L is real, entrywise complex conjugation of the convergent exponential series gives exp(−itL)=conj(exp(itL)), preserving every entry modulus. This observation is on paper; the Lean endpoint directly uses the source's plus sign. We prove the stronger vector equality U_L(π/2)e_u=e_v, which immediately gives the required entry equality.

The corresponding Lean definitions, next to these source conventions, are

```lean
def laplacianPST {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (t : ℝ) : Prop :=
  ‖(NormedSpace.exp (((t : ℂ) * Complex.I) • G.lapMatrix ℂ)) v u‖ = 1

def oddLaplacianClaim : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (G : SimpleGraph (Fin n)),
    ∀ [DecidableRel G.Adj], G.Connected →
      ∀ u v : Fin n, u ≠ v → ∀ t : ℝ, 0 < t →
        ‖(NormedSpace.exp (((t : ℂ) * Complex.I) • G.lapMatrix ℂ)) v u‖ ≠ 1
```

Mathlib's `lapMatrix` is `degMatrix - adjMatrix`. The complex matrix is the entrywise cast of the integer Laplacian, as additionally proved in `complex_laplacian_cast`. `NormedSpace.exp` is the algebra exponential, specialized to the usual matrix product and canonical topology. For complex matrices it is the convergent matrix exponential. Thus the statement concerns precisely exp(itL), without weights or a normalized Laplacian.

## Construction
Fix k ≥ 1 and put r=12k²−1 and c=8k². Then r ≥ 11 and 1 ≤ c ≤ r, since r−c=4k²−1 ≥ 3. Take disjoint vertex sets {u,v}, W={0,1}×(ℤ/rℤ), and R=ℤ/rℤ. Join each of u,v to every vertex of W. For ε∈{0,1}, i∈ℤ/rℤ and 0 ≤ j < c, join (ε,i)∈W to i+j∈R. There are no other edges.

These rules give a simple unweighted bipartite graph, with W as one part and {u,v}∪R as the other. For fixed i, the c shifts are distinct modulo r. Each W vertex has c neighbours in R; each R vertex has 2c neighbours in W (one i=z−j for each shift in each copy). The degrees are therefore 2r at u,v, c+2 on W, and 2c on R. Every W vertex is joined to u; each z∈R is joined to (0,z) by shift zero; and v reaches u through any W vertex. Thus the graph is connected and has odd order 2+2r+r=36k²−1.

## Spectral proof
Let L be its combinatorial Laplacian. Set a=e_u−e_v and p=e_u+e_v. The vertices u,v are nonadjacent twins, so

    La=2r a.

The three-dimensional subspace H of vectors constant on the cells {u,v}, W, R is invariant under L and contains p. For cell values (A,B,C), L produces

    (2r(A−B), 2(B−A)+c(B−C), 2c(C−B)).

Consequently its matrix in cell-value coordinates is

    Q = [ 2r   −2r     0 ]
        [ −2   c+2   −c ]
        [  0   −2c   2c ].

Expanding the determinant gives

    det(tI−Q) = t[t²−(2r+3c+2)t+2c(3r+2)].

Indeed the trace is 2r+3c+2, the sum of principal 2×2 minors is 2rc+4rc+4c=2c(3r+2), and Q has row sums zero. Substitution gives trace 48k² and product 16k²(36k²−1). The discriminant is 64k², so the eigenvalues on H are

    0, 4k(6k−1), 4k(6k+1).

These are distinct for k≥1, so Q is diagonalizable. Equivalently, L restricted to H is symmetric in an orthonormal cell basis. Each eigenvalue on H is divisible by four. The remaining vector needed for e_u is a, whose eigenvalue is 2r=24k²−2 ≡ 2 (mod 4). At t=π/2 the exponential phase is therefore +1 on H and −1 on a. Since e_u=(p+a)/2 and e_v=(p−a)/2,

    exp(iπL/2)e_u = (p−a)/2 = e_v.

Its (v,u) entry is exactly one. This proves PST and refutes the conjecture for every k≥1. No assertion about the full spectrum outside H and the antisymmetric line is required.

## The finite certificate
For k=1, r=11 and c=8. The graph has 35 vertices and 220 edges. In coordinates (u,v;W;R), integer eigenvectors are

    a   = (1,−1;0;0),        eigenvalue 22,
    j   = (1,1;1;1),         eigenvalue 0,
    x20 = (11,11;1;−4),      eigenvalue 20,
    x28 = (−11,−11;3;−4),    eigenvalue 28.

The exact decomposition is

    e_u = a/2 + j/35 + x20/40 − x28/56.

Changing a/2 to −a/2 gives e_v. Lean checks the graph on `Fin 35`, its connectedness, degrees and all four eigenvector identities, the passage from the exponential power series to its eigenvector action, the phases, this decomposition, the exact vector transfer and the conjecture negation. The finite checks use kernel reduction with `decide`. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the endpoint axiom reports. The general construction, characteristic polynomial and infinite-family argument above are paper proofs, not Lean theorems.

The predicate `laplacianPST G u v t` abbreviates the entry-modulus condition at a specified time; by itself it permits u=v and t=0. Distinct vertices and positive time are required by the surrounding `sourceConjecture77` and `source_explicit_counterexample` statements. Thus it is those full statements, rather than the unguarded abbreviation alone, that express transfer between distinct vertices at positive time.

The additional `PSTSource` module states the source's entry definition and its conjecture, proves its equivalence to the reviewed claim by reflexivity, and gives an explicit existential witness in that vocabulary. The four reviewed modules are preserved byte for byte. Full source and rebuild receipts accompany this manuscript.

## Computation and prior work
Claude Opus 5.5's independent review of 20 November 2026 reports an exhaustive enumeration screened numerically for Laplacian PST, with no detected pairs at odd orders 3,5,7,9 (order 1 has no distinct pair). At order 9 it examined 34,209,792 generated graphs, including repetitions, covering every isomorphism type; 32,294,050 of the generated graphs were connected. Its positive controls found known order-4 examples. The spectral screen uses floating-point Jacobi diagonalization and tolerance tests for eigenvalue integrality and spectral projectors; it supplies numerical evidence, not an exact-arithmetic exclusion certificate. These are reported computational findings, not a formal theorem in this packet; we did not rerun that exhaustive computation. They establish no minimality for the 35-vertex witness. Smaller examples of orders 11 through 33 remain possible.

Kirkland, Monterde and Plosker, *Quantum state transfer between twins in weighted graphs* ([arXiv:2201.02720](https://arxiv.org/abs/2201.02720)), give a twin-transfer criterion (Theorem 10). The symmetric/antisymmetric decomposition and arithmetic phase criterion are established tools. The present construction tunes a biregular three-cell quotient to meet that criterion at odd order. Coutinho and Liu, *No Laplacian Perfect State Transfer in Trees* ([arXiv:1408.2935](https://arxiv.org/abs/1408.2935)), exclude odd-order graphs with an odd number of spanning trees, which does not exclude this family. In fact, modulo two the u and v Laplacian columns coincide and their degrees are even. Both the all-ones vector and e_u+e_v belong to the mod-two kernel and are independent. The rank is at most n−2, all (n−1)-minors vanish modulo two, and the matrix-tree theorem shows that the number of spanning trees is even.

Monterde's 2025 Manitoba PhD thesis, *Quantum pure state transfer*, lists the odd-order question as Problem 11 in its future-work section (pp. 163–164), as read by the independent reviewer. The review also screened later related papers and found no public resolution. It reports eleven accessible citing papers out of thirteen counted by OpenAlex; two were unavailable under its daily budget. The reviewer did not read the journal version itself. The discovery lane reports that the published version (*Discrete Mathematics* 349(3), 114832, DOI [10.1016/j.disc.2025.114832](https://doi.org/10.1016/j.disc.2025.114832)) still poses the question. These bounded checks support further review, not a complete priority certificate.

## Significance and limits
The construction supplies an explicit infinite family against the unrestricted odd-order conjecture, while leaving the source's theorems about joins intact. Once the quotient is specified, the proof is short and uses standard spectral tools. Its substantive contribution is the unweighted biregular realization and parameter choice making the symmetric eigenvalues multiples of four while the twin eigenvalue is twice an odd integer. This packet makes no claim of a new general PST criterion, smallest possible counterexample, independently established priority, or formal verification of the entire family. The formal certificate covers the finite counterexample only; the general family has the paper proof given above, and the small-order numerical enumeration is a separate reviewer's reported computation.

# MathDB 378395: the collapsing conjecture is false at (p, q, r) = (4, 4, 5)

Status: draft candidate with zero accepted credit. Root review, independent fidelity review and acceptance are separate.

## Source and literal statement

N. Eriksson, S. E. Fienberg, A. Rinaldo and S. Sullivant, *Polyhedral conditions for the nonexistence of the MLE for hierarchical log-linear models*, arXiv:math/0405044 (J. Symbolic Comput. 41 (2006)), Section 4. The e-print source is in `../sources/math_0405044.eprint`, with its fetch receipt.

Setting (source Section 4): Δ = [12][13][23], the model of no three-factor effect, on a p × q × r table. A_Δ sends a table to its three two-way margins. "The polyhedron P_Δ^{p,q,r} is given by the positive hull of the columns of A_Δ as a cone with pqr extreme rays in R^{pq+pr+qr}." An elementary collapsing replaces a variable X_j and a set S of its states by a new variable with d_j − |S| + 1 states, mapping all states in S to a single state. A collapsing is a sequence of elementary collapsings, viewed as a linear map π : P_Δ^{d} → P_Δ^{d'}. A facet F of P_Δ^{d} is obtained by collapsing if F = π^{-1}(F') for a facet F' of P_Δ^{d'}.

Conjecture (source `conj:col`, MathDB 378395): suppose p ≤ q ≤ r. Then all facets of P_Δ^{p,q,r} are obtained by collapsing from facets of P_Δ^{p,q,q}.

The source verified this computationally for the cases in its Table 1, which stops at 4 × 4 × 4. No 4 × 4 × r table with r > 4 was computed.

## Result

**Theorem.** Let ℓ be the linear functional on R^{16+20+20} given by ℓ(m) = Σ a_ij m^{12}_ij + Σ b_ik m^{13}_ik + Σ c_jk m^{23}_jk, where (rows indexed from 0):

```
a (i×j) = [[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,0]]
b (i×k) = [[0,0,0,0,0],[-1,0,0,0,0],[-1,-1,-1,0,0],[0,-1,0,-1,0]]
c (j×k) = [[1,1,1,1,0],[1,1,1,0,0],[1,0,0,0,0],[0,1,0,1,0]]
```

Then F = {m ∈ P_Δ^{4,4,5} : ℓ(m) = 0} is a facet of P_Δ^{4,4,5}. It is not of the form {m ∈ P_Δ^{4,4,5} : π(m) ∈ F'} for any set F' and any map π induced on margins by state maps s₁ : [4]→[4], s₂ : [4]→[4], s₃ : [5]→[4]. In particular F is not obtained by collapsing from any facet of P_Δ^{4,4,4}, and the conjecture fails for p = q = 4, r = 5.

Write col(i,j,k) = e^{12}_{ij} + e^{13}_{ik} + e^{23}_{jk} for the column of A_Δ indexed by cell (i,j,k). Then w_ijk := ℓ(col(i,j,k)) = a_ij + b_ik + c_jk. Its values, slice by slice (rows i, columns j), are:

```
k=0: [[1,1,1,0],[0,0,0,0],[0,0,1,0],[1,2,2,0]]
k=1: [[1,1,0,1],[1,1,0,2],[0,0,0,1],[0,1,0,0]]
k=2: [[1,1,0,0],[1,1,0,1],[0,0,0,0],[1,2,1,0]]
k=3: [[1,0,0,1],[1,0,0,2],[1,0,1,2],[0,0,0,0]]
k=4: [[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,0]]
```

## Proof

1. **Validity (face).** Every w_ijk ≥ 0. For a nonnegative table x, ℓ(A_Δ x) = Σ_c x_c w_c ≥ 0. So ℓ ≥ 0 on P := P_Δ^{4,4,5}, and F = P ∩ ker ℓ is a face.

2. **dim span P = 44.**
   - *Upper bound.* The 13 margin-consistency relations (row sums of the 12-margin against the 13-margin for each i, of the 12-margin against the 23-margin for each j, and of the 13-margin against the 23-margin for each k) vanish on every column. Twelve of them, ψ₁, …, ψ₁₂, are linearly independent: in reduced row-echelon form they take the values δ_st at twelve pivot coordinates. So span P ⊆ ker ψ, which has dimension 56 − 12 = 44.
   - *Lower bound.* Forty-three tight cells (w = 0) are listed in the certificate. Their columns are linearly independent because there are integer functionals φ₁, …, φ₄₃ with φ_s(col(c_t)) = δ_st. The column col(0,0,0) has ℓ = w_000 = 1, while ℓ vanishes on the 43 tight columns. Hence the 44 columns are linearly independent, and they lie in P.

3. **dim span F = 43.**
   - *Upper bound.* F ⊆ ker ℓ ∩ ker ψ₁ ∩ … ∩ ker ψ₁₂. The 13 functionals are jointly surjective onto R^{13}: the pivot unit vectors realise the ψ coordinates, and col(0,0,0) has ψ = 0 and ℓ = 1. So that intersection has dimension 56 − 13 = 43.
   - *Lower bound.* The 43 independent tight columns lie in F.

   Hence dim span F + 1 = dim span P, so F is a facet.

4. **Not obtained by collapsing.** Let π be induced by state maps s₁, s₂, s₃. Directly from the definition of the collapsed margins, π(col(i,j,k)) = col'(s₁ i, s₂ j, s₃ k). Since s₃ : [5] → [4] is not injective, there are slices k ≠ l with s₃ k = s₃ l. Then π(col(i,j,k)) = π(col(i,j,l)) for all i, j. If F = {m ∈ P : π(m) ∈ F'}, then col(i,j,k) ∈ F ⟺ col(i,j,l) ∈ F for all i, j. But col(i,j,k) ∈ F ⟺ w_ijk = 0, and the five zero patterns above are pairwise distinct. This is a contradiction. The argument uses neither a property of F' nor the special form of the collapsing state maps. ∎

## How the example was found (not needed for the proof)

For fixed [12]-coefficients a, the [13]/[23] coefficients of slice k must form a point of Q(a) = {(u,v) : u_i + v_j ≥ −a_ij}. For an extreme ray of the dual cone, each slice is a vertex of Q(a), up to the shift (u+s, v−s). Q(a) is dual to the regular subdivision of Δ_{p−1} × Δ_{q−1} with heights a. So the non-margin facets correspond to coarsest regular subdivisions together with a choice of cells for the slices, and the largest number of pairwise distinct slice patterns equals the number of maximal cells.

An exhaustive scan used integer heights in {0,1}^9 for 4 × 4 after normalising the first row and column (`scripts/coarse.py`, `logs/coarse-4-4-1.log`). It found 54 height matrices whose coarsest subdivision has 5 cells and 6 with 7 cells. All 60 were verified exactly as facets of P^{4,4,5} or P^{4,4,7} with pairwise distinct slice patterns (`outputs/collapsing-444r-certificates.json`). The 3 × 3, 2 × q, 3 × 4 (heights 0..3) and 3 × 5 (heights 0..1) scans found at most q cells, consistent with the source's Table 1.

## Formal endpoint

`proof/MathDB378395.lean`, theorem `MathDB378395.Main.collapsing_conjecture_false : ¬ MathDB378395.CollapsingConjecture`, and the explicit witness `exists_noncollapsible_facet`. The definitions (`margins`, `marginalCone`, `IsFace`, `IsFacet`, `collapseMap`, `IsElementaryMerge`, `IsCollapsing`, `ObtainedByCollapsing`, `CollapsingConjecture`) are in the same module.

Fidelity notes for reviewers:

- **Face and facet.** A face is the intersection with the kernel of a linear functional that is nonnegative on the cone. A facet is a face whose linear span has dimension one less than that of the cone. This is the standard (Ziegler) notion for polyhedral cones.
- **Collapsing.** It is modelled by the induced fiber-sum map of composite state maps. `IsCollapsing` records sequences of elementary merges. The proof never uses `IsCollapsing`, so the refutation holds for every state-map-induced map, a strictly stronger statement.
- **Scope.** The conjecture is quantified over positive integers p ≤ q ≤ r and refuted at (4,4,5).
- **Kernel computation.** The integer certificate checks use `decide +kernel`, which is kernel reduction, not native code.

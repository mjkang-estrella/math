# I245 — independent complete-rigidity proof gate

**PASS — E4 is proved for attained finite matrix-polynomial witnesses.** No mathematical repair or additional hypothesis is needed. The expanded verifications in [analytic-check.md](../experiments/i245_crouzeix_rigidity_proof/analytic-check.md) make the compressed boundary and interpolation transitions explicit.

**Exact version reviewed:** the completed equality argument in `frontier/experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md`, SHA-256 **`03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627`**. The earlier partial notes in that file are explicitly superseded. The matching final I242 report has SHA-256 `2bba0807883573e6b4287dbb6b1daac0e9cd9169f87ceb6b463d2e36ec12b2e6`.

## Exact approved statement

Assume the complete Crouzeix bound and lower operations stipulated at OpenAI revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Let 1≤n≤4, A∈M_n(C), m≥1 finite, and P an M_m-valued polynomial of arbitrary finite degree. Set M=max_{z∈W(A)}||P(z)||>0. If ||P[A]||=2M, then W(A)=a+ρDbar for some ρ>0. There are unit u,v∈C^m such that p(z)=v*P(z)u satisfies

    ||p(A)||=2M,       max_{W(A)}|p|=M,
    p(a+ρz)=Mηz^k,    |η|=1, 1≤k≤deg P.

An irreducible reducing block B of A realizes ||p(B)||=2M. The scalar geometry step uses Jin v2 Theorem 1, an explicitly identified external theorem. Its finite Schur interpolation Lemma 4 supplies the scalar monomial conclusion. Neither external result is represented as an additional stipulated OpenAI theorem.

## Gate findings

1. **Exterior formula and bound: correct.** Convexity gives Re(1+zh''/h')≥0. The branch normalized at infinity satisfies log(h'/c)=2∫log(1−ξ/z)dμ. Differentiation verifies the plus sign. The probability measure yields |h'|≤4c, with no needed lower derivative bound. Capacity bounds r≤c_j≤R follow from two disk Schwarz arguments.

2. **Boundary limit: paid.** Uniform 1/k Fourier tails give strong L² logarithm convergence. Exponentiation is 4-Lipschitz on the half-plane Re z≤log4, so the derivatives and q_j converge strongly in L². Uniform boundary convergence and normal families identify the exterior map of K. The inverse-map argument can be expanded using |h_j(z)−c_jz|≤2R and |Φ_j(w)|≤(|w|+2R)/r; the limit is nonconstant, has modulus >1, and is inverse to h. The Jordan boundary theorem and local reflection supply the circle interval corresponding to a regular analytic arc. The limit field is therefore the field for K, not an unidentified weak limit.

3. **Fixed-pair normalization: bounded.** The same top singular pair is valid for P/M_j. Interior spectrum of the fixed active block bounds its resolvent on every sufficiently close boundary. Consequently a_j²=||Y*R_jX||²_L² remains bounded while γ_j=2/M_j→2. No uniform Faber collar or lower bound for a_j is assumed.

4. **All residual signs and constants: correct.** Parseval gives C_j=a_j²+3||Y*X||²+Σ_{k≥1}||X*b_kj(B)Y||². Both ordered products and the reciprocal diagonal weights are retained. The exact identity is E_X+E_Y+E_B+2Rres=2(4/γ_j²−1)a_j², with every term nonnegative. It forces X*Y=0 and E_B→0.

5. **Nonlinear passage: correct without a square-root limit.** Expand the difference of tr(H_jDH_jD) and tr(HDHD); strong L² convergence yields L¹ convergence by Cauchy–Schwarz. The limit equals ||H^(1/2)DH^(1/2)||². Its zero integral yields the matrix identity a.e. There is no weak-convergence substitution for this quadratic step.

6. **Isotropy and dimension count: correct.** The matrix identity makes ran H totally isotropic. Orthogonality of ran X and ran Y gives inertia (p,q,d−p−q), so every totally isotropic subspace has dimension at most d−max(p,q). A simple support eigenvalue gives rank H=d−1. Hence p=q=1. The open arc has an open circle-interval preimage; an a.e. identity therefore holds at a point of that arc.

7. **Existence of that arc in every irreducible size ≤4: correct.** A top eigenvalue that is never simple would make both top and bottom multiple. In sizes two and three this makes the pencil scalar. In size four the centered Hermitian generators satisfy H²=aI, K²=bI, HK+KH=2cI. Removing the H component from K produces either a normal pair or two identical 2×2 pairs. Both are reducible. Thus a simple top direction exists. The exact eigenvalue second-derivative formula gives strictly positive curvature, because a zero value would give a common eigenvector of B and B*.

8. **Tensor convention: correct.** With the source's base-first vectorization, write X=ξu^T and Y=ηv^T, not ξu* with the same u. Then x=ξ⊗u, y=η⊗v and y*P[B]x=η*(v*Pu)(B)ξ. This is scalarization of coefficient input vectors; it says nothing about a reducing nilpotent block of P[B].

9. **Reduction and outer summands: correct.** The active irreducible block preserves boundary normalization and excludes boundary spectrum. Its extracted polynomial is bounded on the full W(A). The pin gives ψ(B)=2, exactly Jin's scalar hypothesis. On the resulting disk, the spectral jets of g(z)=p(a+ρz) have minimum H∞ interpolation norm one; radial dilation and polynomial approximation prove this from the pin. Jin's uniqueness then makes g a polynomial finite Blaschke product, hence a monomial. Its bound on W(A) confines all outer summands to the same disk. This final step is necessary and is present.

10. **Companion contract: respected.** The structural companion's common mass-one density represents a similar matrix, whereas the rank argument uses the original matrix's mass-two resolvent field. The proof does not exchange them or infer scalarity merely from a saturated matrix Schur channel.

The full derivations, including an explicit inverse normal-family argument and a radial-dilation proof of the H∞ bound used for interpolation, are in the analytic check. They are expansions of valid steps, not repairs to a false assertion.

## Counterexample pressure and limits

I238's exact weighted chain (1,2,1), obtained from N=[[0,2],[0,0]] and P(z)=[[0,z],[1,0]], remains an obstruction to amplified scalar output rigidity. Its top right singular vector has second iterate norm two, and the scalar square-function sum is 9/4. E4 permits the correct coefficient compression p(z)=z and makes no false output-block claim. Direct sums of disk-contained summands obstruct a whole-matrix Jordan classification but satisfy E4. Nondisk outer summands are excluded by the actual scalar monomial, not by block selection alone. Corners and flat boundary portions do not obstruct the single regular arc needed in the proof.

This gate found no nondisk exact-equality counterexample within the stated quantifiers. It approves neither a quarter-power positive-deficit modulus nor nonattained ψ_cb=2 rigidity. It does not extend E4 to arbitrary base dimension or replace its finite polynomial hypothesis by a rational or general holomorphic witness class.

## Source and contribution assessment

The pinned direct and structural excerpt blocks were read in full, fetched raw pinned manuscripts were independently hashed, and every retained pinned excerpt block was matched verbatim to those raw manuscripts. Both Git blobs match the exact entries of `sources/preprints-tree.json`. This is source-contract and provenance checking, not an audit of stipulated upstream truth.

Jin v2 Sections 1–8 and Corollary 1, including Lemma 4 and the complete proof of Theorem 1, were read in full from the retained primary text; the live primary page confirms version 2, posted 15 September 2026, and the same scalar statement. The retained Åhag–Czyż–Virtanen v3 Section 11 through Corollary 11.5 was read in full. It records the scalar polynomial classification and complete rigidity through size three. The new step reviewed here is the complete residual-to-rank-one reduction and its dimension-four use. No literature-wide novelty certification is implied by this proof gate.

The supplied count remains nine; this review does not edit a shared ledger or independently register a tenth finding. All assigned I245 artifacts and source read extents are indexed in [literature.md](../sources/i245_crouzeix_rigidity_proof/literature.md) and [input-authentication.json](../experiments/i245_crouzeix_rigidity_proof/input-authentication.json).

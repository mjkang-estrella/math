# DRAFT ordinary proof - MathDB 378395

An explicit non-collapsing facet of the 4 × 4 × 5 marginal cone

DRAFT - 1 November 2026. Prepared with AI assistance (OpenAI Codex); no human authorship or affiliation is asserted. This is a candidate manuscript, not an accepted campaign result. Accepted credit: zero. The campaign remains 11/20 beyond the 39 previously credited results; root alone accepts.

Abstract. We give an integral supporting functional for the no-three-way-interaction marginal cone P^{4,4,5}. Its zero face has dimension 43 in a cone of dimension 44. Five distinct labelled layer zero patterns obstruct every state-map pullback to a 4 × 4 × 4 table. Thus the collapsing conjecture of Eriksson, Fienberg, Rinaldo and Sullivant [1, Conjecture 14] fails. An explicit determinant-one minor supplies a finite ordinary facet proof. A byte-preserved Lean certificate proves the negation of the universal conjecture, with a reproducible strict build and declaration audit.

The tropical explanation is logically separate: the five layers describe maximal cells of a regular subdivision of Δ₃ × Δ₃, or equivalently pseudovertices of the associated tropical complex. We derive the marginal-cone bridge here; we do not attribute that statistical statement to the tropical literature. The bounded prior-art review located a relevant reported enumeration by Schröter, but no matching coordinate representative. No priority claim is made.

1. The model and its cone

For positive integers p,q,r, write [d]={0,…,d−1}. The hierarchical model Δ=[12][13][23] has no three-factor effect: its strictly positive distributions have log probabilities of the form αᵢⱼ+βᵢₖ+γⱼₖ (including a normalization constant in these parameters). The sufficient statistic A_Δ sends a real table x to m=(m¹²,m¹³,m²³), with m¹²ᵢⱼ=Σₖxᵢⱼₖ, m¹³ᵢₖ=Σⱼxᵢⱼₖ and m²³ⱼₖ=Σᵢxᵢⱼₖ.

The marginal cone is P^{p,q,r}={A_Δx:x≥0} in V=R^{pq+pr+qr}. Its columns are vᵢⱼₖ=e¹²ᵢⱼ+e¹³ᵢₖ+e²³ⱼₖ, so P is their nonnegative hull. All dimensions below mean dimensions of linear spans. A supported face is P∩ker ℓ with ℓ≥0 on P; a facet has dimension dim P−1. Ambient codimension in redundant margin coordinates is not the facet criterion.

2. Collapsing and the exact conjecture

An elementary collapsing of one variable merges a nonempty subset S of its d states to a single state, retaining the other states, so its new size is d−|S|+1. State relabellings are harmless and allowed. A collapsing is a finite composition of elementary collapsings. It is represented by three composite state maps s₁,s₂,s₃. On margins the induced linear map π sums entries over the corresponding fibers; for example (πm)¹²ᵢ′ⱼ′=Σ_{s₁(i)=i′,s₂(j)=j′}m¹²ᵢⱼ, and similarly for the other two margins.

A facet F of the source cone is obtained by collapsing from a target facet F′ if F={m∈P:πm∈F′}. The intersection with the source cone is part of this definition. In particular, a preimage in all of V is not intended. Direct substitution gives π(vᵢⱼₖ)=v′_{s₁(i),s₂(j),s₃(k)}. Fiber sums compose because summing over composite fibers is an iterated finite sum.

Conjecture 14 of the journal [1], corresponding to conj:col in the arXiv source, states: for all positive integers p≤q≤r, every facet of P^{p,q,r} is obtained by collapsing from a facet of P^{p,q,q}. Equivalently, ∀p,q,r>0 with p≤q≤r, ∀F, Facet(P^{p,q,r},F) implies the existence of a collapsing π to (p,q,q) and a facet F′ of P^{p,q,q} with F=P^{p,q,r}∩π⁻¹(F′). These are the prose and quantified versions used here.

The MathDB record [2] states the same target dimensions, calling P a “polytope.” We use the cone explicitly defined in [1, Section 4]. The earlier assertion that all facets come from binary tables is different: [1, Example 13] already supplies an obstruction at 4 × 4 × 4 to that stronger assertion. A facet at 4 × 4 × 4 alone cannot refute Conjecture 14, since its target is itself.

Theorem. The functional in Section 3 exposes a facet F of P^{4,4,5} which is not a pullback of any subset of the target margin space under any three state maps [4]→[4], [4]→[4], [5]→[4]. Consequently it is not obtained by collapsing from a facet of P^{4,4,4}, and Conjecture 14 is false.

The stronger arbitrary-map, arbitrary-target-set assertion is an ordinary consequence of the same pigeonhole proof. The literal Lean endpoint formalizes the exact conjecture and the required facet obstruction; it does not separately package the stronger assertion as an endpoint.

3. The explicit functional and validity

All indices start at zero. Define ℓ(m)=Σᵢⱼaᵢⱼm¹²ᵢⱼ+Σᵢₖbᵢₖm¹³ᵢₖ+Σⱼₖcⱼₖm²³ⱼₖ by the following matrices (rows in their displayed order).

a = [0 0 0 0]     b = [ 0  0  0  0 0]     c = [1 1 1 1 0]
    [0 0 0 1]         [-1  0  0  0 0]         [1 1 1 0 0]
    [0 0 1 1]         [-1 -1 -1  0 0]         [1 0 0 0 0]
    [0 1 1 0]         [ 0 -1  0 -1 0]         [0 1 0 1 0]

Put wᵢⱼₖ=ℓ(vᵢⱼₖ)=aᵢⱼ+bᵢₖ+cⱼₖ. Its five 4 × 4 slices, with rows i and columns j, are:

k=0         k=1         k=2         k=3         k=4
1 1 1 0     1 1 0 1     1 1 0 0     1 0 0 1     0 0 0 0
0 0 0 0     1 1 0 2     1 1 0 1     1 0 0 2     0 0 0 1
0 0 1 0     0 0 0 1     0 0 0 0     1 0 1 2     0 0 1 1
1 2 2 0     0 1 0 0     1 2 1 0     0 0 0 0     0 1 1 0

Every entry is 0, 1 or 2. Thus ℓ(A_Δx)=Σᵢⱼₖxᵢⱼₖwᵢⱼₖ≥0 for x≥0. Let F=P^{4,4,5}∩ker ℓ. It is a face. Moreover, for any nonnegative representation of a point of F, every positive coefficient must occur at a zero of w: a sum of nonnegative terms is zero only when each term is zero. Hence F is precisely the nonnegative hull of the 45 tight columns. In particular vᵢⱼₖ∈F if and only if wᵢⱼₖ=0.

Write Zₖ={(i,j):wᵢⱼₖ=0}. The sizes are 9,8,8,9,11. Equal sizes do not imply equal labelled sets: the displayed slices show Z₀≠Z₃ and Z₁≠Z₂ as well. Section 5 lists a distinguishing position for every pair, so the non-collapsing argument needs no classification of state maps.

The following dimension argument is over R and uses exact integer data. It is independent of any floating-point hull, tropical correspondence, or enumeration of candidate height matrices.

4. A complete facet certificate

The 13 consistency forms are Rᵢ=Σⱼm¹²ᵢⱼ−Σₖm¹³ᵢₖ (four forms), Sⱼ=Σᵢm¹²ᵢⱼ−Σₖm²³ⱼₖ (four), and Tₖ=Σᵢm¹³ᵢₖ−Σⱼm²³ⱼₖ (five). They vanish on every column. A linear dependence with coefficients uᵢ,vⱼ,tₖ has coordinate coefficients uᵢ+vⱼ, −uᵢ+tₖ, −vⱼ−tₖ. Vanishing forces all uᵢ=tₖ=u and all vⱼ=−u. Thus there is exactly one dependence and the forms have rank 12. Consequently dim P≤56−12=44.

Take the following 43 tight cells, in the stated order. Let B be their 56 × 43 column matrix, ordering coordinates first by 12, then 13, then 23, row-major in each block.

(0, 0, 4), (0, 1, 3), (0, 1, 4), (0, 2, 1), (0, 2, 2)
(0, 2, 3), (0, 2, 4), (0, 3, 0), (0, 3, 2), (0, 3, 4)
(1, 0, 0), (1, 0, 4), (1, 1, 0), (1, 1, 3), (1, 1, 4)
(1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 3, 0)
(2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 0, 4), (2, 1, 0)
(2, 1, 1), (2, 1, 2), (2, 1, 3), (2, 2, 1), (2, 2, 2)
(2, 3, 0), (2, 3, 2), (3, 0, 1), (3, 0, 3), (3, 0, 4)
(3, 1, 3), (3, 2, 1), (3, 2, 3), (3, 3, 0), (3, 3, 1)
(3, 3, 2), (3, 3, 3), (3, 3, 4)

The ordered coordinate rows below select a square submatrix N of B. Its determinant is 1. To specify a directly checkable arithmetic certificate, start N⁽⁰⁾=N and d₋₁=1. At step k=0,…,41, let dₖ=N⁽ᵏ⁾ₖₖ; replace each entry i,j>k by (dₖN⁽ᵏ⁾ᵢⱼ−N⁽ᵏ⁾ᵢₖN⁽ᵏ⁾ₖⱼ)/dₖ₋₁, and zero entries i>k,j=k. No swaps occur. This is fraction-free Gaussian elimination; its final diagonal entry is det N. The row list and every pivot are:

rows: 0 1 19 17 18 2 44 16 3 48 4 21 5 24 36 25
22 23 41 7 8 26 27 28 30 37 38 29 10 42 11 43
32 34 35 13 14 39 15 40 33 47 46
pivots:
1 1 -1 -1 -1 -1 -1 -1 -1 -1 -1 1 1 1 1 1
1 1 1 1 1 -1 1 -1 -1 1 -1 -1 -1 -1 -1 1
1 1 1 1 1 -1 -1 1 1 1 1

This finite recurrence and the column definition verify the determinant claim without an unspecified rank oracle; tools/certificate.py reproduces it. Therefore the 43 tight columns are independent. Since ℓ(v₀₀₀)=1, adjoining v₀₀₀ gives 44 independent columns. Thus dim P=44, ℓ is nonzero on span P, and dim(span P∩ker ℓ)=43. The tight columns give dim F≥43, while F⊆span P∩ker ℓ gives dim F≤43. Hence F is a facet. This completes the facet proof.

5. The obstruction to collapsing

For completeness, these positions distinguish all ten pairs of layers. Each line gives (k,l), then a position (i,j) where exactly one of the two evaluations vanishes. They are read directly from Section 3.

(0,1): (0,2)    (0,2): (0,2)    (0,3): (0,1)
(0,4): (0,0)    (1,2): (0,3)    (1,3): (0,1)
(1,4): (0,0)    (2,3): (0,1)    (2,4): (0,0)
(3,4): (0,0)

Assume F={m∈P:πm∈E} for some subset E of the target margin space and maps s₁:[4]→[4], s₂:[4]→[4], s₃:[5]→[4]. By the pigeonhole principle there are k≠l with s₃(k)=s₃(l). For every i,j, the column-image formula gives π(vᵢⱼₖ)=π(vᵢⱼₗ). Both original columns belong to P. Therefore vᵢⱼₖ∈F if and only if vᵢⱼₗ∈F. By validity and the definition of F, this says wᵢⱼₖ=0 if and only if wᵢⱼₗ=0 for all i,j, contradicting the displayed distinguishing position.

This proof uses neither surjectivity of the maps, nor elementary-merge structure, nor any property of E. It therefore excludes every state map to these target sizes, and in particular every source-defined collapsing and target facet. If variable permutations were also allowed, the target has four states in every variable, so the original five-state factor would still identify two layers and give the same contradiction. No general coordinate-mixing cone automorphism is part of the source definition.

Specializing the universal conjecture to p=q=4,r=5 would assert that this very facet is obtained from P^{4,4,4}. The contradiction refutes the universal statement. This is not an assertion that facets never stabilize: for fixed p,q only finitely many labelled zero patterns can occur. The proposed stabilization threshold q is what fails. Rinaldo [3, Section 4.3.1] already explains the finite-pattern argument following Conjecture 4.3.5.

The result makes no MLE claim for a specific observed table. The relevance to likelihood is the marginal-cone facial description in [1]; the counterexample itself is a statement about facets of that cone. Neither semigroup normality nor Markov-basis degree bounds are substituted for this facial statement.

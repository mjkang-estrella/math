# Literal poset shuffle: incomplete

## Target and actual successor screen

Source: Ayyer–Schilling–Thiéry, `1412.7488v4`, Conjecture 1.1, PDF pp2–3, frozen text lines42–144. For every finite nonchain poset P on n elements, let Ω=L(P), let τ_i swap the adjacent labels at positions i,i+1 only when incomparable, and let T_i,j be the literal sequential path of these blocked swaps (identity for i=j). M=n^(-2)Σ_i,j T_i,j. Target: λ₂(M)≤b_n=1−1/n−2/n², equality iff the comparability graph is disconnected, and nonnegative spectrum. Source's Conjecture 2.2 on O(n log n) mixing is separate. No whole-permutation substitution is made.

The original body was frozen before extraction. The first live queries checked its current version and targeted exact poset successors, before mathematical controls. Current API lists v4, updated13 October2015; journal reference Experimental Mathematics26(1)(2017)22–30. Narrow poset/shuffle query returns only that source; this does not clear literature. The subsequent broader successor screen obtained actual `1509.08580v3` and `2503.17580v4` bodies. See failures.md for the timing limitation: both actual successor bodies were read after the first bounded mechanism controls, rather than before them.

Dieker–Saliola, `1509.08580v3`, text163–169, explicitly states AST's poset conjecture and says its own result gives the antichain case. Its eigenspace construction acts on words/permutations, not arbitrary Ω. Current q-Hecke successor Brauner–Commins–Grinberg–Saliola, `2503.17580v4`, Theorem A(4)/Theorem6.20, supplies a second-eigenvalue formula for R_n,k(q) in the Type-A Hecke algebra. Current API updated28 October2026; body internally dated30 October2026, so these dates are retained distinctly, not silently reconciled. The source's Eq(2.5), text350, requires T_i T_(i+1) T_i=T_(i+1) T_i T_(i+1). On the true three-element V-poset 0<2,1<2, Ω={012,102}, τ_0 is the swap and τ_1=I. Then τ_0τ_1τ_0=I whereas τ_1τ_0τ_1=τ_0. Thus the literal operators are not a module for that q=1 algebra. The nontrivial involution's eigenvalues ±1 also force q=1 in the Hecke quadratic relation (T−q)(T+1)=0. A different intertwining/comparison construction would be a new substantive bridge, not an immediate application. This is a concrete scope obstruction to the strongest located routine-adaptation candidate; it is not a claim that no published theorem could imply the result.

Source-known and not credited: Gram positivity (p2), direct sums of chains Proposition3.1, N-shapes Theorem3.3, disconnected eigenvalue lift Corollary3.6, numerical census all2451 posets through7. r289's206 controls and abstract exponent-six contrary action are reused only as context.

## Route A: insertion/deletion fibers and exact conditional variance

For a fixed element x and a deletion word σ∈L(P\{x}), allowable insertion positions form an interval between the last predecessor and first successor of x in σ. Let k_x(σ) be its length. Under uniform π∈Ω, the deletion word has probability k_x(σ)/|Ω|; conditional on σ, the insertion is uniform. It is generally NOT uniform on L(P\{x}). Example P={0<1}, x=0: deletion words12 and21 have respective fiber sizes1 and2, hence probabilities1/3 and2/3. Ordinary uniform-size-(n−1) induction cannot be used without a weighting correction.

Let H_x be conditional expectation given deletion of x, H=n^(-1)Σ_x H_x. These are orthogonal projections on L²(uniform Ω). Exact law of total variance:

Var(f)=E Var(f|delete x)+Var(E[f|delete x]),
and D_H(f)=⟨f,(I−H)f⟩=n^(-1)Σ_x E Var(f|delete x).

This is a legitimate heat-bath comparison kernel, not an identification with M. In π=012 for P={0<1}, T_0,2 first fails to swap0,1 and then swaps1,2, yielding021. Deleting the originally selected0 and inserting it at the end would be illegal. A blocked path changes which label subsequently moves; any coupling must retain that information.

Tested candidate before further investment: D_M(f)≥D_H(f), equivalently H−M positive semidefinite. Exact Fraction congruence checks pass for all naturally labeled nonchain transitive orders of sizes2,3,4: counts1,6,39, total46. This is bounded support for the bridge, not its proof. Even proving this bridge is insufficient: the requisite sharp Poincaré inequality for H is false in a source-known case.

Explicit P={0<1} with2 isolated, Ω=(012,021,201), n=3:

M=(1/9)[[5,3,1],[3,3,3],[1,3,5]],
H=(1/18)[[11,5,2],[5,8,5],[2,5,11]].

For v=(1,0,−1), Mv=(4/9)v, Hv=(1/2)v, Σv=0. Thus b₃||v||²−vᵀHv=−1/9, while M has the source's sharp disconnected equality. Here H−M has inertia(2,0,1), in fact supplies exactly the extra1/18 in Rayleigh quotient on this mode. The uniform measure divides both quadratic forms by3 and does not change the comparison. A uniform heat-bath argument that ignores the residual loses the constant already here.

Precise gap: prove, for all zero-mean f on every Ω,
D_H(f)+⟨f,(H−M)f⟩≥(n+2)/n² Var(f),
with strictness on connected posets and the equality classification. This is an identity-based target for a corrected fiber theorem, not a proved abstract inequality. Neither positivity of the residual for all P nor the required compensation from variable fiber lengths has been established. Park this route; do not enlarge a census as a substitute.

## Route B: structural relation split, sharp interlacing

Source pp10–11 already proposes deleting a cover and comparing to the two opposite orientations, and warns that rank grows. For an incomparable pair a,b in a base order P, let P⁺,P⁻ add the two orientations with transitive closure. Ω splits as L(P⁺)⊔L(P⁻). Form S=M_(P⁺)⊕M_(P⁻) on the same coordinate space and Δ=S−M_P. If Δ had at most one positive direction, rank-one interlacing would give λ₃(S)≤λ₂(M_P), enabling sharp induction on added relations (the two Perron eigenvalues account for the index shift). The source's N-shape comparison has just this favorable structure. Equality still would require separate control.

Before investing in a general theorem, tested this concrete sufficient condition on literal posets. It fails at the second enumerated split: P is the3-element antichain and split0<1 versus1<0. Ordering Ω=(012,021,102,120,201,210),

9Δ=[[2,1,−2,−1,0,0],[1,0,−1,0,1,−1],[−2,−1,2,1,0,0],[−1,0,1,0,−1,1],[0,1,0,−1,2,−2],[0,−1,0,1,−2,2]].

The principal submatrix on coordinates012,201 is diag(2/9,2/9), hence Δ has at least two positive directions. Exact rational inertia is(2,1,3). This is a true-poset obstruction to the proposed one-positive-direction induction, within source-known direct-chain cases; not a counterexample to either spectral bound. The source's warning about additional rank is quantitatively real at the smallest useful split.

Precise gap: a new structural condition selecting reductions, or a comparison on the subspace orthogonal to both block constants, that preserves b_n and forces strictness for connected P. No such selection theorem or eigenvector-sensitive compensation is obtained. A crude rank bound or rough mixing estimate does not suffice. Park.

## Outcome

No full ordinary endpoint, no PROOF. Both routes expose specific sharp-constant gaps on admissible source-known controls, rather than claiming new cases. The frozen current successor bodies do not demonstrate a complete published subsumer for arbitrary posets. This lane supplies neither a general proof, an admissible counterexample to Conjecture1.1, nor novelty clearance. No acceptance or count request.

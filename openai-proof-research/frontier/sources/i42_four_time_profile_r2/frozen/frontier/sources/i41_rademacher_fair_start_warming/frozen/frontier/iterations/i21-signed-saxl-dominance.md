# I21 — Constructive signed dominance maps, their ranks, and wider-band limits

Date: 2026-10-09. Assumed source revision: **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**. Outcome: **precise investigated gap; no substantial finding submitted for acceptance**. The refined Saxl conjecture is not proved. There is no count change, independent proof/significance acceptance, or worldwide-priority claim.

The suggested simultaneous sign grading does produce actual maps into the two physical flip eigenspaces of the source cyclic module. Those maps are constructed below, without assuming a signed dominance theorem. They fail a required constituent already at order three; an exact Gram-rank computation and an independent central-projection norm certificate identify the failure. The grading itself is the classical alternating-group splitting, rather than new positivity information.

A second repair extends the triangle projection to arbitrary band width, with its physical flip intact. The necessary width to reach a target of width two is at least `ceil((2m+1)/5)`. A third check makes the universal-square companion's column-component separation signed and uses its actual neighboring-column proof. Its available small components still cannot reach the narrow family. These are technical constructions and limits, not an infinite-family support theorem meeting the requested significance standard.

## 1. Exact target, frozen evidence, and independently checked premises

The original assignment is retained verbatim in [full-brief.txt](../sources/i21_signed_saxl_dominance/full-brief.txt). All writes are confined to this report and `frontier/{sources,experiments}/i21_signed_saxl_dominance/`. No agents, shared-index edits, staging, commits, pushes, or other-project changes were made.

Put `rho_m=(m,m-1,...,1)` and `N=m(m+1)/2`. The target is Bessenrodt–Bowman [arXiv:2202.03066v3](https://arxiv.org/html/2202.03066v3), Conjecture 10.2, with the notation of its Section 10:

* For `m>=3`, `Sym² S^{rho_m}` contains every `S^lambda`, `lambda ⊢ N`, except sign when `m≡2 (mod 4)`.
* For `m>=3`, `Λ² S^{rho_m}` contains every such irreducible except `(N)`, `(N-1,1)`, `(N-2,2)`, sign when `m≢2 (mod 4)`, and additionally `(2,2,2)` when `m=3`.

The conjecture follows the all-positive-integer quantifier in Conjecture 10.1. Rather than interpret invalid or coincident small exceptional labels, the literal small squares are recorded: at `m=1`, the symmetric square is `S^(1)` and the exterior square is zero; at `m=2`, they are `S^(3)⊕S^(2,1)` and `S^(1,1,1)`. At `m=3` the exact character check verifies the stated exceptional sets. Neither an unsplit square nor a transpose symmetry of unsplit coefficients resolves this target.

Twenty input snapshots include the rules, pin, catalogue, full preprint tree, shared indexes, full I19, the I17 screen, and I19's source/evidence contracts. The complete tree has 749 manuscript directories, and the read-only cache manifest has 9,340 text records. Every cache record was searched for the saved terms; 101 records matched, mostly irrelevant uses of “tensor square.” Twenty-one selected files from the two directly relevant manuscripts were copied, not the whole cache. Their raw URLs, SHA-256 hashes and Git blob SHA-1 identities are in [pinned-manifest.json](../sources/i21_signed_saxl_dominance/pinned-manifest.json). The retained complete inventory is not the truncated root tree.

Source statement contracts and exact read ranges are in [source-contracts.json](../sources/i21_signed_saxl_dominance/source-contracts.json) and [source-read-passages.json](../sources/i21_signed_saxl_dominance/source-read-passages.json). In particular, the actual proofs of `dominance.tex`, `band-quotient.tex`, `path-band.tex`, and the companion's `balance.tex` and `band.tex` were read. Its capacity theorem and small-degree computations are not substituted for signed results. Its introduction expressly separates ordinary tensor-square universality from BB's refinements.

The following I19 premises were checked against the constructions, not accepted from the parent's validation alone:

1. In the common word realization, position transpose takes the ordered row alternation to the column alternation with scalar one. Thus their actual orbit subspaces coincide. On the generator `w=v_R⊗v_C`, `Fw=t w`; since `F` commutes with the diagonal group action, `W=C[G]w` is flip-stable. This does not identify `F` with the action of `t` on all of `W`.
2. The source high/low projection uses the same threshold in both letters. It commutes with physical flip, preserves each high-position sector under flip, and factors into the smaller flip and the band flip. Its explicit sector-induction inverse also commutes with flip. Thus taking a flip eigenspace preserves the surjection.
3. For width two, both single-layer band spans are the same actual copy of `S^(m,m-1)`. The source's generator-specific four-row support, together with BB Theorem 7.11's **multiplicity-free** entire square, proves equality of the cyclic band with that square. The split by one versus three odd parts is BB's theorem, not new here.
4. Each signed induced quotient gives its own LR lower bound. Separate quotients cannot be added without independence. The width obstruction follows from the maximum possible skew-column length in an LR tableau. It remains valid under perfect smaller induction hypotheses.

The read-only I19 recheck independently reproduces **94 sealed artifacts, 43 pinned files, 117 source contracts, 111 two-row character checks, 458 signed bounds, 434 orthogonality checks, and five literal projection cases**. This is technical evidence validation only, not a fresh proof or significance acceptance. The new deductions below have their own proofs and diagnostics.

## 2. Repair A: actual signed dominance maps

Work over `C`, with ordinary tensor products. Fix `m>=2`, `G=S_{B_m}`, and the actual source Specht subspace `V=C[G]v_R=C[G]v_C`. Write

`v=v_R`, `H=∏_i S_{R_i}`, `u=∑_{h∈H} h v_C`, `x=v⊗u`, `z=v⊗v`.

The source signed average says

`x=∑_{h∈H} sgn(h) h w ∈ W`.                                           (2.1)

The word constant with value `i` along row `i` has coefficient `|H|` in `u`, so `u≠0`. Moreover `hv=sgn(h)v`, `hu=u`; hence `hx=sgn(h)x` and `hz=z`.

### 2.1 The repeated-row module is the whole permutation module

Let `M=C[G/H]`, and define

`Φ:M→Sym²V`, `Φ([gH])=g z`.

This is well-defined and its image is `Z=C[G]z`. The source pair-letter/content map `Q` sends `z` to

`c_m t_m`, where `c_m=(-1)^{∑_{r=1}^m binom(r,2)} ∏_{r=1}^m r! ≠0`,

and `t_m` is constant with output letter `r` on the row of length `r`. Its stabilizer is exactly `H`. Consequently `QΦ` takes distinct coset basis vectors to distinct word basis vectors, each multiplied by `c_m`. Thus **Φ is injective**, and `Z≅M^{rho_m}`. This conclusion uses the source's explicit noncancellation calculation, not just the existence of an irreducible quotient.

For clarity about that calculation: on a row of length `r`, the pair outputs `a_j+b_j-1` have sum `r²`. Their squared sum is at least `r³`, with equality exactly when every output is `r`. The required global content forces equality on every row. The compatible second permutation reverses the first, giving the same product of signs in every retained term. This is the exact hypothesis and role of the source projection.

### 2.2 Keep both commuting involutions

Choose a sign intertwiner `J:V→V`, so

`Jρ(g)=sgn(g)ρ(g)J`.

The `H`-fixed and `H`-alternating spaces of `V` each have dimension one, by Young's rule and the self-conjugacy of `rho_m`. Therefore `J` can be scaled so that `Jv=u`. Schur's lemma gives `J²=κ id`, with `κ≠0`; in particular `Ju=κv`. Set

`T=id⊗J`, `K=(J⊗J)/κ`.

Then `K²=1`, `KF=FK`, and `K` commutes with the diagonal `G` action. Direct multiplication gives

`Tρ⊗²(g)=sgn(g)ρ⊗²(g)T`, `TFT^{-1}=KF`, `TKT^{-1}=K`.       (2.2)

For example, `FT=(J⊗id)F=TKF`; this is precisely the extra factor omitted by an invalid uniform-sign twist.

By (2.1), `Tx=κz`, so `Z⊂TW`. Although **no invariance of W under K is assumed**, `TW` is invariant under `KF`, because `W` is invariant under `F`. Since `F` fixes every vector of `Z`, this implies `KZ⊂TW`. It follows that

`(1+δK)Z ⊂ TW`, with joint eigenvalues `(F,K)=(+1,δ)`, for `δ=±1`.

Applying `T^{-1}` sends this space into `W^δ`. On the generator,

`T^{-1}(z+δKz)=κ^{-1}(v⊗u+δu⊗v)`.                         (2.3)

Thus the following are actual equivariant maps, with no unproved positivity in their definition:

`Ψ_δ:M^{rho_m}⊗sgn → W^δ`,

`Ψ_δ([gH]⊗1)=sgn(g) g(v⊗u+δu⊗v)`.                         (2.4)

Changing `g` to `gh`, `h∈H`, gives two cancelling signs; this proves well-definedness. Left multiplication verifies equivariance with the sign-twisted domain. Membership in `W^δ` follows already from (2.1), `F`-stability and direct symmetrization; (2.2) explains the relation to dominance and the proposed grading.

The combined map `(Ψ_+,Ψ_-)` is injective. Indeed, the sum of its two components is twice the signed-coset map generated by `x`, whose image is `T^{-1}Z` and which is injective by §2.1. This proves ordinary dominance with multiplicities, but **does not make either component injective**.

### 2.3 The exact missing rank

Equip `V` with its invariant positive Hermitian form. The normalized `J/√κ` can be taken unitary with square one, so `K` is a self-adjoint involution. On `M`, let

`A=Φ*Φ`, `B=Φ*KΦ`.

Here `A` is positive definite. The Gram operators of the projected maps `(1+δK)Φ` are `2(A+δB)`. Thus for `τ ⊢ N`, the multiplicity in their images is

`rank((A+δB)|_{M[τ]}) / dim S^τ`.                           (2.5)

After twisting, this is the multiplicity of `S^{τ^t}` in the image of `Ψ_δ`. Formula (2.5) is an exact characterization of these **constructed maps**, not a replacement hypothesis for a theorem. No lower bound ensuring the desired nonzero ranks for all dominated partitions is proved.

The eigenvalues of `A^{-1/2}BA^{-1/2}` lie in `[-1,1]`; they can reach the endpoints. A positive ordinary Kostka multiplicity therefore supplies neither of the two separate ranks. Nor may `K` simply be transported to `M` as an endomorphism: `KZ=Z` has not been established.

## 3. A concrete failure of Repair A, and its classical grading explanation

### 3.1 Exact matrices for the actual source vectors

For `m=3`, use the row-major order

`(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)`

on the six positions. The experiment constructs the literal row/column alternating words, the twelve-element row subgroup, and `u=∑_H h v_C`. It obtains

`⟨v,v⟩=12`, `⟨u,u⟩=540`, `κ=45`.

These numbers and the sign intertwiner are checked without inferring its sign from BB: for every `g∈S_6`, the exact identities

`⟨u,gu⟩=45 sgn(g)⟨v,gv⟩`,

`⟨u,gv⟩=sgn(g)⟨v,gu⟩`

show that the map `gv↦sgn(g)gu` is well-defined, has adjoint equal to itself and square `45 id`. The first identity identifies the Gram kernels and the scale of the invariant form; the second identifies the adjoint. No numerical eigensolver is used.

The 60 cosets give explicit Gram matrices for (2.4). Exact integer row elimination after applying central idempotent matrices gives these image multiplicities on all dominated types:

| `lambda` | `im Ψ_+` | `im Ψ_-` | full `Sym²V` | full `Λ²V` |
|---|---:|---:|---:|---:|
| `(3,2,1)` | 1 | 1 | 3 | 2 |
| `(3,1,1,1)` | **0** | 1 | **1** | 3 |
| `(2,2,2)` | 1 | 0 | 2 | 0 |
| `(2,2,1,1)` | 1 | 2 | 1 | 2 |
| `(2,1,1,1,1)` | 1 | 1 | 1 | 1 |
| `(1,1,1,1,1,1)` | 1 | 0 | 1 | 0 |

The full image dimensions are 36 and 49. In particular `(3,1,1,1)` is a nonexceptional target killed by the symmetric map. Seeding order three separately is possible, so this does **not** prove that the maps fail at all larger orders. It does invalidate the proposed unrestricted “both dominance projections are nonzero” shortcut.

### 3.2 A short, exact zero-projection certificate

Here is a separately reproducible certificate for the bold entry, rather than merely a rank assertion. Put `y=v⊗u+u⊗v`. For a cycle type `μ`, define

`C_μ=∑_{g of type μ} ⟨y,gy⟩`.

Each summand is exactly

`2(⟨v,gv⟩⟨u,gu⟩+⟨v,gu⟩⟨u,gv⟩)`.

In the order

`(6),(5,1),(4,2),(4,1²),(3²),(3,2,1),(3,1³),(2³),(2²,1²),(2,1⁴),(1⁶)`,

the two integer lists are

`C_μ/6480 = (-20,33,12,-18,11,-40,11,-1,21,-11,2)`,

`χ^(3,1³)(μ) = (-1,0,0,0,1,1,1,2,-2,-2,10)`.

Their dot product is zero. The character list can independently be obtained as the coefficient of `t³` in

`(∏_{a∈μ}(1-(-t)^a))/(1+t)`,

since this hook is `Λ³` of the standard representation. The correlation list is a finite sum of the displayed integer word pairings, all reproduced by the supplied script.

For the orthogonal central projector

`e_λ=(dim S^λ/720)∑_{g∈S_6} χ^λ(g^{-1})g`,

we have `||e_λ y||²=⟨y,e_λ y⟩=0`. Positive definiteness gives `e_λ y=0`, and centrality kills its **entire cyclic span**, proving the zero map. This use of a constituent projector and a positive norm is not an inference of support from a scalar trace heuristic. The full symmetric multiplicity one follows independently from the ordinary character-square formula, and the full character data are retained.

### 3.3 The extra grading is already the alternating-group splitting

Normalize `J²=1` for this paragraph. On `Res_{A_N}V`, its two eigenspaces are the two classical irreducible constituents `V_+,V_-`. Then, on restriction to `A_N`,

`(F=+,K=+) = Sym²V_+ ⊕ Sym²V_-`,

`(F=-,K=+) = Λ²V_+ ⊕ Λ²V_-`,

and each of `(F=+,K=-)` and `(F=-,K=-)` is a copy of `V_+⊗V_-`.

This follows by expanding `(V_+⊕V_-)²` and taking flip eigenvectors in the mixed terms. It is the same decomposition behind BB Lemma 2.3 and Theorem 6.1. Bessenrodt's [arXiv:1704.00707v1](https://arxiv.org/abs/1704.00707), Section 2, gives the corresponding difference-character formula on the two split principal-hook classes. No novelty is claimed for it.

For precision, let `d` be the diagonal length of `rho_m`, `h` its partition of principal hook lengths, and `σ=(-1)^((N-d)/2)`. Let `g_λ` be the ordinary square multiplicity and `t_λ` the symmetric minus exterior multiplicity. The multiplicity in the **full-square** joint sector is

`b_{f,k}(λ) = (g_λ + f t_λ + k σ χ^λ(h) + fk t_{λ^t})/4`.      (3.1)

To derive it, use the projector `(1+fF)(1+kK)/4`. The four traces against `ρ⊗²(g)` are respectively `χ(g)²`, `χ(g²)`, `tr(Jρ(g))²`, and `sgn(g)χ(g²)`. The difference character `tr(Jρ(g))` vanishes off the split principal-hook type and its square there is `σ z_h`, where `z_h=∏h_i`. Character inner products give (3.1). This is a classical character identity, not rank control for the subspace `Z`.

It explains the order-three failure more strongly. For `τ=(4,1,1)`, `m=3`, the four full-square multiplicities in the order `(+,+),(+,-),(-,+),(-,-)` are

`0,1,2,1`.

For example `g_τ=4`, `t_τ=t_{τ^t}=-2`, `χ^τ(5,1)=0`, and `σ=1`. A vector in the symmetric `τ`-space before the one-factor twist can consequently supply only the **exterior** `τ^t=(3,1³)` after twisting. The symmetric copy of `(3,1³)` comes from the exterior, `K=-` sector before twisting. Merely replacing `z` by more symmetric repeated-row vectors cannot supply this particular missing copy. A repair would need additional pre-twist exterior vectors, or a genuinely different construction.

## 4. Repair B: arbitrary-width signed triangle quotients

The source restricts its stated band proposition to `s=1,2`. The following extension proves the map for every width; it makes no assumption about the band's constituents.

**Proposition.** For integers `m>=2` and `1<=s<=m-1`, put `h=m-s`, `D=B_h`, `A=B_m\D`, and

`L=|A|=s(2m-s+1)/2`, `θ_{m,s}=(m,m-1,...,m-s+1)`.

Let `U_{m,s}` be generated by the ordered row and column alternations on `A`, in alphabet `1,...,s`. The two single-layer orbit spaces are the same actual copy of `S^{θ_{m,s}}`; `U_{m,s}` is a flip-stable submodule of its square. There is a surjection

`W_m^ε → Ind_{S_D×S_A}^{S_{B_m}} ⊕_{ab=ε}(W_h^a ⊠ U_{m,s}^b)`.   (4.1)

**Proof.** Project at each position onto pair letters either both `<=s` or both `>s`. Retained high positions have row and column counts `r_i=max(h+1-i,0)`. For each prefix `k`,

`∑_{i<=k}r_i=∑_j min(k,r_j)`.

Each column contributes at most its summand on the right. Equality forces every column of positive count `r_j` to put all of its high positions in its first `r_j` rows. Thus the high set is exactly `B_h`. This argument does not use `s<=2`.

On a block of length `r`, write `a=max(r-s,0)` and `b=min(r,s)`. Its retained alternation factors with shuffle sign `(-1)^{ab}` into the high initial position segment and the low terminal segment. Row and column length lists agree, so the product of their shuffle signs is one. The projected generator is therefore exactly `w_h`, with both alphabets shifted by `s`, tensored with `u_{m,s}`.

The subgroup orbit is the full outer tensor product. Its distinct translated high-position sets are disjoint coordinate sectors, so the explicit sector-induction map and inverse from the source give the full induced image. The projection, letter shift, sectors, and inverse all commute with physical flip. On the regrouped tensor flip is `F_h⊗F_U`. Taking its `ε` eigenspace proves (4.1).

Finally the band row lengths are `s` repeated `m-s+1` times followed by `s-1,...,1`. The alternating-block Specht type is their conjugate, namely `θ_{m,s}`. Position transpose maps the row vector to the column vector, proving equality of the actual spaces and flip-stability of the cyclic tensor. ∎

No equality `U_{m,s}=(S^{θ_{m,s}})²` is asserted for `s>=3`. Ordinary band support would not prove it, since these larger squares need not be multiplicity-free.

### 4.1 A linear-width requirement, even with perfect signed bands

**Proposition.** If the ordinary induced module underlying (4.1) contains `S^λ`, and `w=λ_1`, then necessarily

`2m+1 <= (2w+1)s`.                                          (4.2)

**Proof.** The band lives in `(C^s⊗C^s)^{⊗L}`. Schur–Weyl duality therefore bounds every constituent `η` by `length(η)<=s²`, even if the cyclic band is replaced by the entire square. A positive coefficient `c_{ν,η}^λ` requires an LR tableau of `λ/ν` with entries in `1,...,length(η)`. Strict column increase permits at most `s²` boxes per skew column. There are at most `w` columns. Hence `L<=ws²`. Substitute the displayed value of `L`, divide by positive `s`, and rearrange. ∎

For `λ=(2^{floor(N/2)},1^{N mod 2})`, this gives

`s >= ceil((2m+1)/5)`.

Thus every fixed finite menu of band widths eventually misses this nonexceptional family, even under perfect hypotheses on every smaller staircase **and** every signed band square. Width three is already excluded by this size obstruction for `m>=8`. Taking `s=m` would leave the empty triangle and `U_{m,m}=W_m`; it merely restates the original problem.

### 4.2 What the width-three experiment does and does not say

Literal expansion verifies the new projected-generator identity at `(m,s)=(4,3)`; an all-low `(4,4)` check tests the tautological endpoint separately. Each examines 82,944 input pair words.

For the stronger, optimistic target in which `U_{m,3}` is replaced by the **entire** square of `(m,m-1,m-2)`, exact character/LR calculations show:

* At `m=4`, target `(5,5)` has optimistic signed multiplicities `(3,0)`, while the staircase square has `(4,2)`. Thus even full band support would not give this exterior target through that one cut.
* At `m=5`, the width-two target `(2^7,1)` has optimistic values `(6,4)`, compared with actual `(54,49)`. At `m=6`, `(2^10,1)` again has optimistic values `(6,4)`; its full staircase square was not computed in this experiment.

The latter values are **upper bounds on what this cyclic-band quotient can certify**, not established lower bounds for `W_m`. To turn them into a support proof requires nonzero pairings for the actual cyclic `U_{m,3}^±`. The two-row multiplicity-free argument is unavailable. This explicitly identifies the unproved burden rather than hiding it inside “wider bands have the expected support.”

## 5. Repair C: the companion's column-component separation with flip retained

The companion offers a route using the full staircase square rather than the single row-column orbit. We tested its actual separation construction, including the dual coordinate-line proof, instead of dismissing every appearance of a symmetric tensor as irrelevant.

Partition the staircase's column blocks among disjoint components `D_i`. In a component let `X_i` be the single-layer Specht span of its column alternations. Choose disjoint, ordered output intervals `I_i` for `a+b-1`, as in `lem:balance-separation`, and let `P_i` be the local coordinate projection, with image `Y_i=P_i(X_i⊗X_i)`.

**Signed separation.** There is a quotient of the full square whose signed decomposition is

`(S^{rho_m}⊗S^{rho_m})^ε → Ind_{∏S_{D_i}}^{S_N} ⊕_{∏ε_i=ε} ⊠_i Y_i^{ε_i}`.  (5.1)

**Proof.** The actual subgroup subspace in each layer is `⊠X_i`, generated independently in the two layers. Each component's position count and output sum are fixed: `d_i=∑r`, `σ_i=∑r²`, summing its column lengths. The global coordinate projection imposes the corresponding counts and sums in the ordered intervals. The source's separation argument forces the positions with outputs in `I_i` to be precisely the prescribed component positions: exchanging any positive number of positions across an interval boundary strictly changes their sum while preserving their count. Remove the first component and iterate.

Thus the local full-square subspace projects onto `⊠Y_i`, and its translates have disjoint coordinate supports. Their sum is the full induced module. Since output `a+b-1` is symmetric, the global projection, each local projection and each coordinate sector commute with physical flip, which acts on the local product by the product of the local flips. The global image may have other vectors; take the orthogonal projection onto this invariant induced submodule, using the invariant word inner product. That projection commutes with `G` and `F`, and is onto because the local product is already in the image. Composition gives (5.1); taking eigenspaces proves its displayed split. ∎

For neighboring column lengths `r,r-1`, source `bal:neighboring` gives every type with at most four rows after projection to `[r-1,r]`. The single-layer type is `(2^{r-1},1)`, the transpose of `(r,r-1)`. Twisting **both** factors preserves physical flip, and BB Theorem 7.11 computes its full square. Since this square is multiplicity-free and the projected image has its entire support, the local projection is injective as well as onto its image. Its signed constituents consequently have the known one/three-odd-part split. This is a legitimate use of the companion and supplies actual signed local modules, not ordinary support relabelled as signed support.

It nevertheless fails the narrow-family test. If components are single columns or neighboring pairs, the longest column `m` is either alone, supplying only `(m)`, or paired with `m-1`, supplying a size `2m-1` constituent of length at most four. For a width-two target, LR containment makes the first option impossible when `m>2`, and the second impossible when `2m-1>8`, i.e. `m>=5`. Thus no arrangement of these available components reaches the width-two family in that range.

More generally, if every component contains at most `r` columns, the single-layer type has width at most `r`; after simultaneous sign conjugation its square has constituents of length at most `r²`. The component containing the length-`m` column has at least `m` positions. A width-two final target forces each local LR constituent to fit inside that target, so its area is at most `2r²`. Hence **`m<=2r²` is necessary** for any such component construction, regardless of the output intervals or the optimistic full local supports. In particular, bounded numbers of columns per component do not solve the gap either. This is only a necessary condition, not a sufficiency theorem for growing components.

The companion's repeated symmetric-pair lemma concerns `Sym^a(Sym²E)` in a pair-letter space. Its generic common linear maps need not commute with pair-letter transpose. Its nonzero ordinary contractions therefore supply no unproved flip locations for larger components. For an actual signed test one must show

`⟨u+εFu,t⟩=⟨u,t+εFt⟩ ≠ 0`

on a specified irreducible dual test space. Separate nonvanishing of the two ordinary contractions does not exclude their identical cancellation.

## 6. Current primary comparison and significance limits

The current BB abstract page retrieved on 2026-10-09 still identifies v3, dated 2023-01-18. Its full HTML bytes are identical to the retained I19 copy. The published [Algebraic Combinatorics article](https://alco.centre-mersenne.org/articles/10.5802/alco.294/) is dated 2023-08-29. The live version pages, full primary manuscript bytes, retrieval hashes, queries, raw search outputs, exact statement contracts and proof-read passages are retained under the assigned source directory.

The direct comparisons checked were:

* BB Lemmas 2.1, 2.3 and 2.4: square characters, restriction splittings, and linear-character twists. Proposition 2.5: the already-known symmetric semigroup property. These do not prove nonzero ranks of (2.4).
* BB Theorem 3.7 and the nearby modular identities: the known diagonal staircase splitting and weighted relations do not assign both signs to each desired constituent. BB Theorem 5.2 proves the three uniform exterior exceptions. Theorem 6.1/Corollary 6.2 locate sign, and Theorem 6.3 treats near-sign types. None is counted as an I21 result.
* BB Theorems 7.8, 7.11 and 7.15: established two-row splittings and vanishing statements. They are inputs or duplicate exclusions, not a new constituent theorem.
* Ikenmeyer [arXiv:1410.6549v2](https://arxiv.org/abs/1410.6549), current version dated 2015-05-05: Theorem 2.1 and Sections 4–5 give ordinary dominance support. Its reduction from dominated to dominating targets transposes two Kronecker labels; it does not state that this one-factor sign operation has a uniform physical-flip sign.
* Bessenrodt [arXiv:1704.00707v1](https://arxiv.org/abs/1704.00707), dated 2017-04-03: Section 2's alternating-group split and principal-hook difference values are the existing ingredients of (3.1). Its spin/critical-class ordinary support criteria are not silently treated as signed positivity.

A wrong initial publisher DOI ending `alco.19` is explicitly marked as a rejected retrieval; the correct Bessenrodt DOI is `alco.18`. No statement from that wrong page is used. An initially guessed width-three zero example was also rejected when exact arithmetic contradicted it; the retained exploration log identifies it. The report uses only the corrected examples above.

The bounded current searches did not locate a primary theorem furnishing the missing all-target ranks, but this is not evidence of worldwide novelty. More decisively, this report has no new substantial support family to submit: the principal outputs are explicit maps, a finite failure certificate, and necessary width conditions. Even if useful for the next attempt, they should not be padded into a substantial finding.

## 7. Reproduction, seal, drift, and precise handoff

Run from the project root:

```sh
python frontier/experiments/i21_signed_saxl_dominance/recheck_i19.py
python frontier/experiments/i21_signed_saxl_dominance/check.py
python frontier/experiments/i21_signed_saxl_dominance/verify.py
```

The I21 diagnostic constructs exact word vectors, subgroup sums, all permutation actions for `S_3` and `S_6`, and rational/integer Gram data. It computes ranks of central-isotypic Gram matrices with integer row operations and gcd reduction, not ranks modulo a prime or a floating tolerance. The central-projection norm certificate is stored separately from the full-square character computations. It also checks arbitrary-width literal projections, optimistic width-three LR multiplicities, and all four joint-character sectors for `m=2,3,4,5`. These finite checks substantiate the displayed finite examples; the general map and obstruction claims are proved in §§2, 4 and 5.

The verifier checks the sealed files, frozen input bytes, 21 selected source Git/SHA identities against the complete tree, exact source and primary-contract slices, current primary retrieval hashes, and deterministic diagnostic reproduction. Shared-index differences are reported separately as live drift; the frozen premises are not rewritten. [verification.json](../experiments/i21_signed_saxl_dominance/verification.json) is the authoritative drift/verification record. The shared indexes were not edited by I21.

**Observed drift, separately:** both `frontier/README.md` and `frontier/TEN-FINDINGS.md` changed after the I21 snapshots. Their frozen and current hashes are in the verification record. No other live input drift was observed. Verification passes for 80 sealed artifacts, 20 frozen inputs, 42 source contracts, 14 primary contracts, 928 full-square joint-sector multiplicities, 28 constructed-map constituent ranks, 1,452 intertwiner Gram identities, and two new literal projection cases.

**Remaining mathematical work.** A continuation must construct nonzero pre-twist exterior vectors or another family of flip-compatible pairings covering the deficient grades, with a uniform constituent-by-constituent rank argument. Alternatively it must prove signed support for actual cyclic bands of growing width (at least (4.2) for a given narrow target), or for sufficiently large companion components, and prove LR coverage with the precise BB exceptions. Equation (2.5), full-square sector traces, perfect smaller hypotheses, and hypothetical full band squares are not substitutes for those steps. Small bases can be settled directly but do not provide the missing uniform mechanism.

**Disposition:** investigated gap, with explicit constructions and a sealed reproducible handoff. No viable substantial candidate is asserted, and no acceptance or ledger action is requested.

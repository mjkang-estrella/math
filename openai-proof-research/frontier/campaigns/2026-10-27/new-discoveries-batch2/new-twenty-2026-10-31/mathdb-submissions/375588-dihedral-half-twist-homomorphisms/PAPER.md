# Dihedral relations for overlapping interval half twists in the positive braid monoid

Claude Opus 5.5 developed the original proof, performed the first review and wrote Lean stage 1. GPT-6.2 Sol performed the cross-model review, then wrote the direct positive derivation and Lean stage 2. A separate GPT-6.2 Sol lane performed the final check and edited this manuscript. The final checker uses the same model family as the stage-2 packager.

## Abstract

We prove all three families in Berenstein, Greenstein and Li's Conjecture 6.35. The two prescribed interval half twists satisfy the length-N alternating relation in the positive braid monoid. The proof computes the common alternating word by splitting the half twists into block crossings and internal twists. For cases I and II a descending rotation absorbs the crossings. Case III lifts a four-strand identity to blocks of widths (p,p,r,p). Lean proves the positive equality and constructs the homomorphism from the presented dihedral Artin monoid using explicit triangular words for the two images. Section 1 identifies these words with the source's longest-element lifts using the type-A inversion formula and the Matsumoto–Tits word property.

## 1. The conjecture and the source's definitions

Conjecture 6.35 of Berenstein, Greenstein and Li, arXiv:2606.26776v2, §6.5, p. 78, concerns integers with 1 ≤ b ≤ a < n − 1 and a > 1. It asks for a homomorphism Br⁺(I₂(N)) → Br⁺_n that sends the two generators to T_{w∘^{[1,a]}} and T_{w∘^{[b,n−1]}}, respectively, whenever any of the following conditions holds.

1. N = 2n/(n + b − a − 2) is a positive even integer.
2. a + b = n and N = n/(b − 1) is an odd integer of at least 3.
3. a + 1 = 2(b − 1), a + b < n and N = 6.

The authors report verifying the conjectures in §6.5 for n ≤ 15. The same statement appears as Conjecture 5.85 in their 2024 preprint arXiv:2405.18821v5, §5.12. These are MathDB records 375588 and 363298 for a single conjecture.

In the source's Artin presentation (§2.3), each pair of distinct generators with finite Coxeter parameter m has an alternating relation of length m. By §5.2, Br⁺_n is the monoid of type A_{n−1}, with generators σ_1, …, σ_{n−1}. It has the relations σ_iσ_j = σ_jσ_i for |i − j| ≥ 2 and σ_iσ_{i+1}σ_i = σ_{i+1}σ_iσ_{i+1}. The source monoid Br⁺(I₂(N)) has generators T̂1, T̂2 and the single relation alt_N(T̂1, T̂2) = alt_N(T̂2, T̂1), where alt_N(x,y) starts with x and alternates for N factors.

For a finite parabolic subgroup W_J, §2.4 writes w∘^J for its longest element. By Theorem 2.3, any reduced expression of w in simple reflections gives the same positive lift T_w on replacing each reflection by the corresponding Artin generator.

So the assignments define a homomorphism Br⁺(I₂(N)) → Br⁺_n exactly when

  alt_N(X, Y) = alt_N(Y, X) in Br⁺_n, where X = T_{w∘^{[1,a]}}, Y = T_{w∘^{[b,n−1]}}.

**Half twists.** For 1 ≤ u ≤ v ≤ n put

  Δ[u,v] := ∏_{k=u}^{v−1} (σ_k σ_{k−1} ⋯ σ_u)   (left to right in k; Δ[u,u] = 1).

The word s_u (s_{u+1}s_u) ⋯ (s_{v−1}⋯s_u) is a reduced expression of the longest element w∘^{[u,v−1]} of the parabolic subgroup ⟨s_u, …, s_{v−1}⟩ ≅ S_{v−u+1}. Its image in S_n is the reversal of the interval [u,v]. Induct on the interval width. After reversing the first v−u strands, the last descending run moves the final strand to the front and shifts the other strands one position right, preserving their reversed order. That reversal is the unique permutation attaining all C(v−u+1, 2) possible inversions within the interval. This is also the number of letters of the word. In S_n the Coxeter length equals the inversion count, so the word is reduced and represents the longest element of the parabolic subgroup. By the Matsumoto–Tits word property in the source's Theorem 2.3, Δ[u,v] = T_{w∘^{[u,v−1]}}. In particular X = Δ[1,a+1] and Y = Δ[b,n]. Lean proves the equality of the two explicit word evaluations (`halfTwistP_eq_H`) and the letter count C(m,2) for every width m (`hwL_length`). It checks the triangular word's permutation evaluation on every interval 1 ≤ u ≤ v ≤ n for n ∈ {4, 6, 7} (`halfTwist_image_reversal`). The general reversal, reducedness and identification with T_w are the argument on paper above.

## 2. The positive identities

For the rest of the proof work in the positive braid monoid. The calculations use associativity, the unit and the Artin relations. The resulting identities therefore hold for the images of the generators under any homomorphism to a monoid. Write Δ_m = Δ[1,m], Δ = Δ_n, and interpret the half twist of a block of width 0 or 1 as the unit. Write H(u,w) for the half twist of the w strands after the first u strands and B_u(W) for the product of half twists of consecutive blocks of width pattern W beginning at that offset. Use B for B_0 and W^t for t repetitions of W. Products of internal braids on disjoint blocks commute, since their generator indices differ by at least two.

Set p = b−1, q = n−1−a and j = p+q. Then X = Δ_{n−q} and Y = H(p,n−p). The hypotheses in the three cases become:

1. N = 2m, m ≥ 1 and mj = n.
2. p = q, N = 1+2k with k ≥ 1 and Np = n.
3. a+1 = 2p, n = 3p+r with r ≥ 1 and N = 6.

Indeed q ≥ 1 by a < n−1. In case II, p = 0 would give b = 1 and a = n−1, contradicting the same inequality. Thus the denominators in cases I and II are positive, and cross multiplication gives equivalent integer conditions. In case III, 1 < a and a+1 = 2p imply p ≥ 2, and a+b = 3p. We will prove the common positive words are Δ^{2m−2} B((p,q)^m), Δ^{N−2} B(p^N) and Δ² h₁²h₂²h₃h₄² in cases I, II and III, respectively. The h_i are the four block half twists defined below.

## 3. Proof

### 3.1 Half twists

Let D_m := σ_mσ_{m−1}⋯σ_1 and A_m := σ_1σ_2⋯σ_m, so that Δ_{m+1} = Δ_m D_m by definition.

**Lemma 1.** For 1 ≤ i ≤ m−1, σ_iD_m = D_mσ_{i+1} and A_mσ_i = σ_{i+1}A_m. *(Lean: `s_mul_D`, `A_mul_s`.)*
*Proof.* Induct on m, with the assertion vacuous at m ≤ 1. For i ≤ m−2, σ_i commutes with σ_m, and the inductive hypothesis applies. For i = m−1, use σ_{m−1}σ_mσ_{m−1} = σ_mσ_{m−1}σ_m and the fact that σ_m commutes with D_{m−2}. The proof for A_m is symmetric. ∎

**Lemma 2.** (a) Δ_{m+1} = A_mΔ_m. (b) Δ_mσ_i = σ_{m−i}Δ_m for 1 ≤ i ≤ m−1. *(Lean: `Hw_succ_A`, `Hw_mul_s`.)*
*Proof.* (a) Induction: Δ_{m+2} = A_mΔ_m·σ_{m+1}D_m = A_mσ_{m+1}Δ_mD_m = A_{m+1}Δ_{m+1}, because Δ_m commutes with σ_{m+1}. (b) Induction on m. For i ≥ 2, Δ_{m+1}σ_i = Δ_mD_mσ_i = Δ_mσ_{i−1}D_m = σ_{m+1−i}Δ_{m+1} by Lemma 1. For i = 1 and m ≥ 2, Δ_{m+1}σ_1 = A_mΔ_mσ_1 = A_mσ_{m−1}Δ_m = σ_mA_mΔ_m by (a), induction and Lemma 1. For the step from m = 1 to m = 2, the only index is i = 1 and both sides are σ₁². ∎

**Lemma 3.** (a) A_mD_{m+1} = D′_mA_{m+1}, where ′ denotes translation by 1. (b) Δ_{m+1} = Δ′_mA_m. (c) The word of Δ_m with every σ_i replaced by σ_{m−i} also evaluates to Δ_m. *(Lean: `A_mul_D`, `Hw_succ_sh`, `Hw_flip`.)*
*Proof.* (a) At m = 0 both sides are σ₁. For the inductive step, write A_{m+1}D_{m+2} = σ₁A′_mD′_{m+1}σ₁ = σ₁D″_mA′_{m+1}σ₁, where ″ is translation by 2. Since A′_{m+1} = σ₂A″_m and σ₁ commutes with both doubly shifted runs, this is D″_m(σ₁σ₂σ₁)A″_m. The braid relation changes it to D″_mσ₂·σ₁σ₂A″_m = D′_{m+1}A_{m+2}. (b) At m = 0 both sides of the claimed identity are the unit. Then Δ_{m+2} = Δ′_mA_mD_{m+1} = Δ′_mD′_mA_{m+1} = Δ′_{m+1}A_{m+1}. (c) Induction on m. Under the reversal, the defining word Δ_mD_m of Δ_{m+1} becomes (the reversed word of Δ′_m)·A_m. By induction this equals Δ′_mA_m, which is Δ_{m+1} by (b). ∎

Two operations on words preserve the Artin relations. Reflection R replaces σ_i by σ_{n−i}. Reversal reads the letters in the opposite order and reverses the order of products. By Lemma 3(c) reflection sends H(u,w) to H(n−u−w,w). Therefore R fixes Δ and carries B_u(W) to B_{n−u−ΣW}(W reversed), using commutation of the internal twists to restore the block order. Word reversal fixes each half twist by induction, since the reversed word of A_mΔ_m evaluates to Δ_mD_m. Reflecting Δ_{m+1} = A_mΔ_m in its own interval gives the fourth form Δ_{m+1} = D_m H(1,m). Finally, applying Lemma 2(b) twice shows that Δ² commutes with each generator. The corresponding Lean facts include `reflect_H`, `Bk_reflect`, `Hw_op`, `Hw_succ_right` and `fullTwist_commutes`.

### 3.2 Rectangular crossings

Let C(x,y) exchange a block of x strands with the block of y strands to its right. Use the explicit word D_x·D_x@1···D_x@(y−1), where @u adds u to each index. This word moves the strands of the right block to the left in their order, one per run. Its two splittings are

  C(x,y+z) = C(x,y) C(x,z)@y,  
  C(x+y,z) = C(y,z)@x C(x,z).

The first follows from the definition. For the second, split each descending run D_{x+y}@t into D_y@(t+x) D_x@t. If i < t, the largest index in D_x@i is x+i and the smallest in D_y@(x+t) is x+t+1, so the two runs commute. Collecting the y-runs first yields the formula. In particular C(x,1) = D_x and C(1,y) = A_y. These are `crossL_add`, `Cr_horiz`, `Cr_one_right` and `Cr_one_left`.

The shift rules through C(x,y) are σ_i C(x,y) = C(x,y) σ_{i+y} for 1 ≤ i < x and σ_i C(x,y) = C(x,y) σ_{i−x} for x < i < x+y. For the left block, apply the descending rule of Lemma 1 through each row of the word. For the right block, induct on x, starting with C(0,y) = 1. The second splitting gives C(x+1,y) = A_y@x · C(x,y). For x+1 < i < x+1+y, the ascending rule of Lemma 1 gives σ_i A_y@x = A_y@x σ_{i−1}. The inductive rule lowers i−1 by x. Induction on a word transports any internal braid by applying the rule to its generators. Internal braids on external blocks commute with the crossing by their index gaps. These are `s_mul_Cr_left`, `s_mul_Cr_right` and the word transport lemmas in `BraidCross` and `BraidFat`.

The half-twist split is Δ_{x+y} = Δ_x C(x,y) Δ_y = Δ_x H(x,y) C(x,y). For the first equality induct on y, starting with y = 0. The new descending run D_{x+y} = D_x@y · D_y follows Δ_y. Its first factor commutes with Δ_y and extends C(x,y), while Δ_y D_y = Δ_{y+1}. The right shift rule gives the second equality. These are `Hw_add_cross'` and `Hw_add_cross`.

Three adjacent block crossings satisfy the cabled braid relation. For widths (x,y,z), the word crossing the left position first is C(x,y)·C(x,z)@y·C(y,z). The word crossing the right position first is C(y,z)@x·C(x,z)·C(x,y)@z. Use the first splitting to turn the initial two crossings on the left into C(x,y+z). Transport the following C(y,z) to its left, which places it at offset x. On the right, the last two crossings combine to C(x,z+y) = C(x,y+z) by the same splitting. Crossings between disjoint pairs commute by their index gaps. Each local move updates the width pattern identically on both sides. Thus any positive Artin move in the fat word can be lifted, even within a longer word. Lean proves these facts in `Cr_YB` and `mvs_F`.

### 3.3 Rotation and overlapping half twists

Put ρ = D_{n−1}. The descending shift of Lemma 1 gives Zρ^s = ρ^s Z@s whenever Z uses only indices at most n−1−s. Two identities for ρ will be used.

First, Δ_{n−k}ρ^k = ΔΔ_k for 0 ≤ k ≤ n. For the induction from k to k+1 let m = n−k−1 and write ρ = U D_m with U = D_k@m. The braid Δ_m commutes with U, so Δ_m ρ^{k+1} = U Δ_{m+1} ρ^k = U Δ Δ_k. Lemma 2(b) moves U past Δ and replaces it by A_k, and A_k Δ_k = Δ_{k+1}. The base k = 0 is immediate. At k = n this gives ρ^n = Δ². These are `positive_complement` and `positive_rho_full`.

Second, for x+l = n,

  ρ^l = H(x,l) C(x,l) Δ_l.                                             (1)

For l = 0 all factors are the unit. At l+1, use the l formula with first width x+1 and prepend ρ = (D_l@x) D_x. The factor D_x commutes with H(x+1,l). Then (D_l@x) H(x+1,l) = H(x,l+1) by the fourth half-twist form. In the middle use C(x+1,l) = C(x,l)@1 · A_l and D_x·C(x,l)@1 = C(x,l+1). The remaining A_lΔ_l equals Δ_{l+1}. This proves (1), formalized as `rho_rotation`.

Now let p+q+l = n. The left half-twist split of H(p,q+l) is H(p,q) H(p+q,l) C(q,l)@p. Use Δ_{p+l} = Δ_p C(p,l) Δ_l for the second half twist. The Δ_p factor commutes past the preceding three factors, and C(q,l)@p · C(p,l) = C(p+q,l). Equation (1) gives

  H(p,q+l) Δ_{p+l} = B(p,q) ρ^l.                                     (2)

This is `rho_overlap`.

### 3.4 Cases I and II

Let W be a width pattern of total j and t ≥ 1 with tj ≤ n. We claim

  (B(W)ρ^{n−j})^t = Δ^{2(t−1)} ρ^{n−tj} B_{n−tj}(W^t).                 (3)

At t = 1 the descending shift moves B(W) through ρ^{n−j}. For the induction to t+1 with (t+1)j ≤ n, prepend B(W)ρ^{n−j} and move it past the central power Δ^{2(t−1)}. The run exponents (n−j) and (n−tj) add to n + (n−(t+1)j). Replace the first n runs by Δ², move that central factor to the front and shift B(W) through the remaining run power. Its translated offset is u = n−(t+1)j. The previous product of block twists starts at u+j, so appending those factors gives B_u(W^{t+1}). All shifts lie within n strands by the bound on tj. This is `positive_block_pow`.

In case I, (2) gives YX = B(p,q)ρ^{n−j}. Apply (3) at t = m, giving (YX)^m = Δ^{2(m−1)} B((p,q)^m). Apply this calculation with p and q exchanged to the reflected generators. Reflection interchanges the two half-twist positions, fixes Δ, and reverses the pattern ((q,p)^m) back to ((p,q)^m). Thus (XY)^m has the same value. This proves `caseI_positive`.

In case II use W = (p,p) and t = k in (3). Here n−2kp = p and alt_N(X,Y) = X(YX)^k. After moving the central term to the front, the left factors are Xρ^p = ΔΔ_p by the first rotation identity. Appending B_p(W^k) to Δ_p gives B(p^N). Thus the value is Δ^{2(k−1)+1} B(p^N). Reflection swaps X and Y and fixes the whole expression by its constant width pattern. This proves `caseII_positive`.

### 3.5 Case III

Cut the strands into four consecutive blocks of widths (p,p,r,p). Write h_i for the half twist inside block i. For a word in the three block generators, denote by F its positive lift starting at this width pattern and using the rectangular crossing for each successive pair of widths. The two-block half-twist split gives X = h₁h₂ F(σ₁). For Y, split at the boundary after block 2, then split the half twist on blocks 3 and 4. The crossing σ₃ puts their widths in order (p,r). The remaining crossing C(p,p+r) splits in the right width and gives the crossings σ₂σ₃. Thus Y = h₂h₃h₄ F(σ₃σ₂σ₃). Both block words preserve the width pattern. The transport rule gives

  XY = h₁²h₂h₃h₄ F(γ),  where γ = σ₁σ₃σ₂σ₃.

The permutation induced by γ cycles positions 1, 2 and 4 and fixes 3. Move the internal twists of the displayed product to the right of the fat word and cube. Each of the cycled blocks gathers 2+1+1 = 4 twists, and block 3 gathers 3. Thus (XY)³ = F(γ)³ h₁⁴h₂⁴h₃³h₄⁴.

On four strands put d = σ₃σ₂σ₃σ₁σ₂σ₃. It is the positive half twist by Lemma 3(b) applied at width four, since the translated triangular word σ₂σ₃σ₂ equals σ₃σ₂σ₃ by the adjacent braid relation. The following is a chain using Artin relations, with digits denoting the generator indices:

```text
132313231323
312313231323
312133231323
321233231323
321232321323
321323321323
323123321323
323123323123
```

Thus γ³ = d², and cabling this chain gives F(γ)³ = F(d²). To compute Δ², split Δ at the boundary after the first block, and split the remaining three-block half twist as above. The last three blocks reverse first, and the first block crosses the newly ordered three in succession. The result is Δ = h₁h₂h₃h₄ F(d). In the second copy of Δ, the starting widths are the reverse of the first widths. Move its four internal twists left through the first F(d) using transport. They contribute one more half twist on each original block. Hence Δ² = h₁²h₂²h₃²h₄² F(d²). The product h₁²h₂²h₃²h₄² commutes with F(γ), since γ permutes the blocks and every exponent in that product is two. Consequently

  (XY)³ = (h₁²h₂²h₃²h₄² F(γ)³) h₁²h₂²h₃h₄²
        = Δ² h₁²h₂²h₃h₄².

Word reversal fixes all the internal half twists. They commute with each other and with Δ². The displayed expression is therefore invariant under reversal, while the reversal of (XY)³ is (YX)³. This proves `caseIII_positive`. In Lean, the seven moves are checked by `chain_ok`. Cabling and transport are `mvs_F` and `hpN_mul_F`. The two positive computations of the full twist and the cube are in `caseIII_positive_closed`.

### 3.6 The homomorphism

For even N = 2m the alternating words are (XY)^m and (YX)^m. For odd N = 1+2k they are X(YX)^k and Y(XY)^k. The computations above give the equality in Br⁺_n for each branch. The single defining relation in Br⁺(I₂(N)) therefore holds on the proposed images. The universal property of the monoid presentation gives the homomorphism with those generator images.

## 4. Lean statements

`BrPlus n` is `PresentedMonoid (braidRelsPlus n)` on `Fin (n - 1)`, with the length-three adjacent relations and length-two nonadjacent relations. Index i represents σ_{i+1}. `DihedralPlus N` is `PresentedMonoid (dihedralRelsPlus N)` on `Fin 2`, with the pair of alternating positive words as its defining relation. `halfTwistP` evaluates the triangular word written in §1. The proof of `halfTwistP_eq_H` identifies it with the interval word used by the calculations. `Hyp` expresses the baseline inequalities together with the three cases in §2. The endpoints in namespace `BGL` are:

```lean
theorem conj_6_35_monoid (n a b N : ℕ) (hyp : Hyp n a b N) :
    alt N (halfTwistP n 1 (a + 1)) (halfTwistP n b n) =
      alt N (halfTwistP n b n) (halfTwistP n 1 (a + 1))

theorem conj_6_35_monoid_hom (n a b N : ℕ) (hyp : Hyp n a b N) :
    ∃ φ : DihedralPlus N →* BrPlus n,
      φ (PresentedMonoid.of (dihedralRelsPlus N) 0) = halfTwistP n 1 (a + 1) ∧
      φ (PresentedMonoid.of (dihedralRelsPlus N) 1) = halfTwistP n b n
```

The proofs use the positive relations directly, and the axiom audit is included in the report. The stage 1 group endpoints and the conditional monoid endpoint are retained as earlier results. The infinite hypothesis families in `BraidNonVacuity` give instances of each positive endpoint. The finite checks there distinguish the two alternating words at length N−1 in the braid group in selected instances by their permutation images.

## 5. Significance

With empty decorations, the source's Theorem 6.6 gives case II at N = 3, and Theorem 6.11 gives case I at N = 4 with b ≥ 2. The rotation factorization extends the computation uniformly in the widths and in N. The unequal-width lift in case III reduces the infinite family to seven local braid moves and an internal twist calculation. Together these identities establish the existence of the specified homomorphisms for the three parameter families.


## 6. Prior art

The 2026 arXiv record lists v1 and v2, both of which state the conjecture. The earlier preprint states it as Conjecture 5.62 in v3, 5.73 in v4 and 5.85 in v5. The final review found no journal version in the arXiv records or the Crossref title searches. OpenAlex lists zero citing works for the 2026 preprint and one for the 2024 preprint, *Noncommutative marked surfaces II* (arXiv:2507.20393), which addresses a different problem. The authors' *Hecke monoids, their homomorphisms and parabolicity* (arXiv:2605.09761v3) addresses Hecke monoids. The closest related follow-up found was Vidur Sury's 2026 thesis, whose indexed abstract concerns classification for domain Br⁺₃.

The local Principia index and registry snapshots yielded no matching resolution. Earlier reviews checked the live omega registry, but a GitHub API rate limit prevented a fresh search in the final review. The thesis was screened by its indexed abstract. These searches did not identify a public proof of all three families.

## References

* A. Berenstein, J. Greenstein, J.-R. Li, Artin monoids, their homomorphisms and twins, arXiv:2606.26776v2 (2026).
* A. Berenstein, J. Greenstein, J.-R. Li, Hecke and Artin monoids and their homomorphisms, arXiv:2405.18821v5 (2024).
* J. Tits, Le problème des mots dans les groupes de Coxeter, Symposia Math. 1 (1969), 175–185.
* A. Björner, F. Brenti, Combinatorics of Coxeter Groups, GTM 231, Springer 2005 (Prop. 1.5.2: length = inversions in S_n).

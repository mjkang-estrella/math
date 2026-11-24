# One-step separation of genus-g Tutte polynomials

*A machine-checked proof of Conjecture 5.12 of Miezaki, Oura, Sakuma and Shinohara (MathDB 361823).*

Proof candidate: GPT-6.1 Sol lane `t1-pool071-proof-sol61-20261120-r1`. Review: Claude Opus 5.5 lane
`t1-prelean-X40-opus-20261120-r1`. Lean formalization and this write-up: Claude Opus 5.5 lane
`genus-tutte-separation-361823-formal-paper-opus55-20261120-r1`, 2026-11-20. Every statement below marked
**[Lean]** is proved in Lean 4.34.1 with Mathlib `d13f23b` (appendix `LEAN-SOURCE-APPENDIX.md`). The endpoint
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. Final check: Claude Opus 5.5 lane
`t1-final-check-361823-opus55-20261120-r1`. This lane is the same model family as the formalizer and the
pre-Lean reviewer; the proof candidate is from a different family.

## 1. The conjecture and the source definitions

Source: T. Miezaki, M. Oura, T. Sakuma, H. Shinohara, *The Tutte polynomials of genus g*, arXiv:2402.06845v1
(10 Feb 2024; v1 is the only version and there is no journal reference).

**Conjecture 5.12 (p. 27), verbatim.** "There exist two infinite sequences of matroids {M_i} and {N_i} such
that T^(g)(M_i) = T^(g)(N_i) and T^(g+1)(M_i) ≠ T^(g+1)(N_i)."

The `g` is the arbitrary positive integer of the preceding Proposition 5.10 (verbatim): "For any positive
integer g, there exist two positive numbers c1, c2 and two infinite sequences matroids {M_i} and {N_i} such
that T^(g)(M_i) = T^(g)(N_i) and T^(⌈c1 g+c2⌉)(M_i) ≠ T^(⌈c1 g+c2⌉)(N_i)." The source introduces it with
"As a direct consequence of Theorem 4.22, we obtain the following proposition". Theorem 4.22 gives one pair
`M, N` per `g` with `T^(g)` equal and `T^(⌈√2 g⌉)` different. So in the source, "infinite sequences" is
reached directly from one pair per `g`. The conjecture follows Problem 5.11 ("Find two infinite sequences of
matroids {M_i} and {N_i} such that the constant c1 is as small as possible") with the words "More precisely,
we have the following conjecture". It is the case `c1 = c2 = 1`.

Two readings of the quantifiers are possible:
- **(R1)** for every `g ≥ 1` there are sequences `(M_i, N_i)_{i ∈ ℕ}` with the property;
- **(R2)** there are sequences `(M_g, N_g)_{g ≥ 1}` with `T^(g)(M_g) = T^(g)(N_g)` and
  `T^(g+1)(M_g) ≠ T^(g+1)(N_g)`, with the index running with the genus.

The source attaches no further condition: not non-isomorphism beyond what the inequality forces, not
connectedness, not simplicity, not representability. The Lean theorem below is (R1), and (R2) follows from
it (Corollary in §2). The MathDB record (361823) states the conjecture as printed, with "Let `g` be a
positive integer".

**Definition 1.3 (p. 4), verbatim.** "Let M := (E, I) be a matroid. Let (A_i | i = 1, ..., g) be an arbitrary
g-tuple of subsets of E. Let Λ1 := {1, ..., g} and let Λ2 := binom(Λ1, 2). For every element λ ∈ Λ2, let us
denote A∩(λ) := ∩_{i∈λ} A_i and A∪(λ) := ∪_{i∈λ} A_i. By using these notations, let us define

  T^(g)(A_1, ..., A_g) := Π_{λ∈Λ1} (x_λ − 1)^{ρ(E)−ρ(A_λ)} (y_λ − 1)^{|A_λ|−ρ(A_λ)}
      × Π_{λ∈Λ2} (x_{∩(λ)} − 1)^{ρ(E)−ρ(A∩(λ))} (y_{∩(λ)} − 1)^{|A∩(λ)|−ρ(A∩(λ))}
      × Π_{λ∈Λ2} (x_{∪(λ)} − 1)^{ρ(E)−ρ(A∪(λ))} (y_{∪(λ)} − 1)^{|A∪(λ)|−ρ(A∪(λ))}.

Then the genus g Tutte polynomial T^(g)(M) of the matroid M will be defined as follows:
T^(g)(M) := Σ_{A_1,...,A_n ⊆ E} T^(g)(A_1, ..., A_g)." (The source's `A_n` is a typo for `A_g`.)

Rank (p. 2): "The rank ρ(A) of an arbitrary subset A of E is the cardinality of the largest independent set
contained in A." Tutte polynomial (p. 3): "T(M; x, y) = Σ_{A⊂E} (x − 1)^{ρ(E)−ρ(A)} (y − 1)^{|A|−ρ(A)}."

**Lean counterparts** (module `GTDefs`, printed by the clean build):

```lean
abbrev Slot (h : ℕ) := Fin h ⊕ ({p : Fin h × Fin h // p.1 < p.2} × Bool)   -- inl i = λ ∈ Λ1;
                                                    -- inr (p,false) = ∩(p), inr (p,true) = ∪(p), p ∈ Λ2
def slotSet (A : Fin h → Finset α) : Slot h → Finset α
  | Sum.inl i => A i
  | Sum.inr (p, false) => A p.1.1 ∩ A p.1.2
  | Sum.inr (p, true) => A p.1.1 ∪ A p.1.2
noncomputable def genusTutte (h : ℕ) {α} [Fintype α] [DecidableEq α] (M : Matroid α)
    (_hE : M.E = Set.univ) : MvPolynomial (Slot h × Bool) ℤ :=        -- (s,false) = x_s, (s,true) = y_s
  ∑ A : Fin h → Finset α, ∏ s : Slot h,
    (X (s, false) - 1) ^ ((M.eRk Set.univ).toNat - (M.eRk (slotSet A s : Set α)).toNat) *
    (X (s, true) - 1) ^ ((slotSet A s).card - (M.eRk (slotSet A s : Set α)).toNat)
```

`Matroid` is Mathlib's matroid and `Matroid.eRk` is Mathlib's rank (the supremum of the cardinalities of
independent subsets, in `ℕ∞`; finite here, so `toNat` loses nothing). This Mathlib revision has no ℕ-valued
`Matroid.rk`, which the review's sketch mentions. Every slot has its own pair of variables, as in the source.

## 2. The theorem

**Theorem [Lean `GenusTutte.miezaki_conj_5_12`].** For every integer `g ≥ 1` there are `n : ℕ → ℕ` strictly
increasing and matroids `M_i, N_i` on `Fin (n i)` (ground set everything) such that for every `i`,
`T^(g)(M_i) = T^(g)(N_i)` and `T^(g+1)(M_i) ≠ T^(g+1)(N_i)`.

```lean
theorem miezaki_conj_5_12 (g : ℕ) (hg : 0 < g) :
    ∃ (n : ℕ → ℕ) (M N : ∀ i, Matroid (Fin (n i))) (hM : ∀ i, (M i).E = Set.univ)
      (hN : ∀ i, (N i).E = Set.univ),
      StrictMono n ∧ ∀ i, genusTutte g (M i) (hM i) = genusTutte g (N i) (hN i) ∧
        genusTutte (g + 1) (M i) (hM i) ≠ genusTutte (g + 1) (N i) (hN i)
```

This is the review's endpoint word for word except `M.rk X` → `(M.eRk X).toNat` and `B s A` → `slotSet A s`.
For each `g`, the sequences come from a single pair by adding `i` loops. The source likewise calls its
sequences (Proposition 5.10) a "direct consequence" of a single pair per `g` (Theorem 4.22), though it does
not say how it builds them. `StrictMono n` forces ground sets of different sizes, so the members of each
sequence are pairwise non-isomorphic. For each `i`, `M_i` and `N_i` are non-isomorphic because their
genus-`(g+1)` polynomials differ.

**Corollary (reading (R2)).** There are matroids `M_g, N_g` (`g ≥ 1`) with `T^(g)(M_g) = T^(g)(N_g)` and
`T^(g+1)(M_g) ≠ T^(g+1)(N_g)` for every `g`. *Proof:* take `i = 0` in the theorem for each `g`. ∎ For `g ≥ 4`
these are the parity gadgets of §3.5 with no loops added. They form one explicit family in which `g` is the
dimension of the cube.

## 3. Proof

Throughout, a *tuple* is `A = (A_1, …, A_h)` of subsets of a finite ground set, `B_s(A)` is its slot set at
slot `s`, and for any `ρ : 2^E → ℕ`, `R ∈ ℕ` we write

  `gt_h(ρ, R) = Σ_A Π_s (x_s − 1)^{R − ρ(B_s)} (y_s − 1)^{|B_s| − ρ(B_s)}`,

so `T^(h)(M) = gt_h(ρ_M, ρ_M(E))` by definition [Lean `genusTutte_eq_gt`, `rfl`].

### 3.1 Sparse paving matroids with loops [Lean `GTSparse`]

Let `N ⊆ E`, `r ≥ 1`, and `𝓗` a family of `r`-subsets of `N` with `|H ∩ H′| ≤ r − 2` for distinct members.
Call `I` independent iff `I ⊆ N`, `|I| ≤ r` and `I ∉ 𝓗`.

*Axioms.* `∅` is independent since members of `𝓗` are nonempty. If `I ⊆ J` with `J` independent and `I ∈ 𝓗`,
then `|I| = r ≥ |J|` forces `I = J ∈ 𝓗`, impossible. Augmentation: let `|I| < |J|`, both independent, and
`e ∈ J ∖ I`. `I + e ⊆ N` and `|I + e| ≤ |J| ≤ r`. If `I + e ∈ 𝓗` then `|I| = r − 1` and `|J| = r`, so `J ⊄ I + e`
(else `J = I + e ∈ 𝓗`); pick `f ∈ J ∖ (I + e)`. If also `I + f ∈ 𝓗`, the two distinct members `I + e, I + f`
share `I`, of size `r − 1 > r − 2`. So `I + f` is independent. (Built with Mathlib's `IndepMatroid.ofFinset`.)

*Rank formula.* `ρ(S) = min(r, |S ∩ N|) − [S ∩ N ∈ 𝓗]`. Upper bound: an independent `F ⊆ S` lies in `S ∩ N`, has
`|F| ≤ r`, and if `S ∩ N ∈ 𝓗` it cannot equal `S ∩ N`, so `|F| ≤ r − 1`. Lower bound: if `S ∩ N ∈ 𝓗` delete one
element; if `|S ∩ N| ≤ r` and `S ∩ N ∉ 𝓗` take `S ∩ N`; if `|S ∩ N| > r` take an `(r+1)`-subset `T` and two of its
`r`-subsets `T − x`, `T − y`: they meet in `r − 1` elements, so not both lie in `𝓗`.

A *gadget* is the loopless case `N = E`; its rank is `ρ_𝓗(B) = min(r, |B|) − [B ∈ 𝓗]` [`Gadget.rank`].

### 3.2 Equality by a "Miss" bijection [Lean `sum_miss_eq`]

**Lemma 1.** Let `α, β` be finite, `ρ, ρ′` functions on their subsets, `K` a finite linearly ordered index set,
`φ_k : α → β` bijections and `Bad_k`, `Bad′_k` families of subsets (`k ∈ K`) with

- (H1) `φ_j(B) ∈ Bad′_k ⇔ B ∈ Bad_k` for all `j, k, B`;
- (H2) `B ∉ Bad_k ⇒ ρ′(φ_k B) = ρ(B)`.

Let `Miss(A) = {k : no slot set of A lies in Bad_k}` (and `Miss′` with `Bad′`). Then the sums of the summands
of `gt_h(ρ, R)` over tuples with `Miss ≠ ∅` and of `gt_h(ρ′, R)` over tuples with `Miss′ ≠ ∅` are equal.

*Proof.* Slot sets commute with applying a bijection to every probe, so by (H1) `Miss′(φ_j A) = Miss(A)` for every
`j`. Map `A ↦ φ_{k(A)} A` with `k(A) = min Miss(A)`; the inverse is `A′ ↦ φ_{k′(A′)}^{-1} A′` with `k′ = min Miss′`.
Since `k(A) ∈ Miss(A)` no slot set of `A` is in `Bad_{k(A)}`, so by (H2) every slot keeps its size and its
`ρ`-value, hence the summand. ∎

### 3.3 Inequality by one coefficient [Lean `gt_ne_of_witness`]

**Lemma 2.** Suppose `ρ ≤ R`, `ρ ≤ |·|` on both sides, and there is a tuple `A₀` on `α` such that no tuple on
`β` has the same pair `(|B_s|, ρ′(B_s)) = (|B_s(A₀)|, ρ(B_s(A₀)))` at every slot `s`. Then
`gt_h(ρ, R) ≠ gt_h(ρ′, R)`.

*Proof.* Substitute `x ↦ x + 1`, `y ↦ y + 1` (an algebra map). Each summand becomes the monomial with
exponents `(R − ρ(B_s), |B_s| − ρ(B_s))_s`, which determine `(|B_s|, ρ(B_s))` under the two bounds. The
coefficient of the monomial of `A₀` counts the tuples with the profile of `A₀`: at least 1 on `α`, 0 on `β`. ∎

### 3.4 Loop padding and assembly [Lean `GTPad`]

For a gadget `(α, r, 𝓗)` and `i ∈ ℕ`, place `α` and `i` loops on `Fin(|α| + i)` (`Gadget.pad`). Transporting along
`α ⊕ Fin i ≃ Fin(|α| + i)` and splitting each probe into its `α`-part and loop part, the slot sizes add and the
rank only sees the `α`-part, so

  `T^(h)(pad_i) = gt_h(ρ_𝓗, ρ_𝓗(α)) · L_{h,i}`,  `L_{h,i} = Σ_{A ⊆ loops} Π_s (y_s − 1)^{|B_s|}`

[`Gadget.genusTutte_pad`]. `L_{h,i} ≠ 0` (at all variables `= 2` it is the number of tuples) and
`ℤ[x, y]` is a domain, so equality and inequality pass to all paddings. Hence two gadgets of equal size `a`
with equal genus-`g` and different genus-`(g+1)` polynomials give the theorem for `g` with `n i = a + i`
[`conj_of_gadgets`].

### 3.5 Genus g ≥ 4: parity gadgets [Lean `Parity`, `Rigidity`, `ParityGenus`]

Let `t = g ≥ 4`, `E_p = {x ∈ {0,1}^t : Σ x_i ≡ p (mod 2)}` (`p = 0, 1`), `S_p(k, c) = {x ∈ E_p : x_k = c}`,
`𝓗_p = {S_p(k, 1) : k < t}`, `r = 2^{t−2}`. Flipping coordinate `j` is a bijection `τ_j : E_0 → E_1`.

*Counts.* `|E_p| = 2^{t−1}`, `|S_p(k,c)| = 2^{t−2}`, `|S_p(k,c) ∩ S_p(k′,c′)| = 2^{t−3}` and
`|S_p(k,c) ∪ S_p(k′,c′)| = 3·2^{t−3}` for `k ≠ k′`. (Flipping a coordinate outside the constrained ones swaps
parities, and flipping a constrained coordinate swaps its value.) Hence `r ≥ 1` and distinct members of `𝓗_p`
meet in `2^{t−3} ≤ r − 2` elements (as `t ≥ 4`): both are gadgets of size `2^{t−1}` and rank `r`.

*Surjectivity.* For distinct `k₁, k₂, k₃` and any bits there is `x ∈ E_p` with those three coordinates: fix
them, set the rest to 0, and if the parity is wrong flip a fourth coordinate (`t ≥ 4`).

**Rigidity Lemma [Lean `Parity.rigidity`].** If every `k < t` is *hit* by `A` (some slot set equals
`S_p(k, c)` for some `c`), then every `k` is hit by a singleton slot (`A_i = S_p(k, c)`).

*Proof.* Choose a slot `σ_k` hitting `k` and write `T_k = B_{σ_k}(A) = S_p(k, c_k)`. Each slot is either an
intersection over its input set `In(σ) ⊆ [t]` or a union over it (singletons count as intersections;
`|In| ∈ {1, 2}`). By surjectivity onto two coordinates no `T_k ⊆ T_{k′}` (`k ≠ k′`), and onto three
coordinates neither `T_{k₁} ∩ T_{k₂} ⊆ T_k` nor `T_k ⊆ T_{k₁} ∪ T_{k₂}` for distinct `k, k₁, k₂`.

*Every output has a private input*, i.e. some `a ∈ In(σ_k)` lies in no `In(σ_{k′})`, `k′ ≠ k`. Otherwise, with
`In(σ_k) = {a, b}` (`a = b` allowed), pick `k₁, k₂ ≠ k` with `a ∈ In(σ_{k₁})`, `b ∈ In(σ_{k₂})`; then
`In(σ_k) ⊆ In(σ_{k₁}) ∪ In(σ_{k₂})`. If `σ_k` is an intersection: if `σ_{k₁}` is a union, `T_k ⊆ A_a ⊆ T_{k₁}`;
likewise for `σ_{k₂}`; if both are intersections, `T_{k₁} ∩ T_{k₂} ⊆ T_k` (or `T_{k₁} ⊆ T_k` when `k₁ = k₂`).
If `σ_k` is a union, the dual inclusions hold. Each case contradicts surjectivity.

A choice of private inputs `π : [t] → [t]` is injective (a private input of `k` is in no other input set), hence
bijective. If `In(σ_k)` had a second element `b`, then `b = π(k′)` for some `k′`, and `b ∈ In(σ_k)` forces
`k′ = k`, so `b = π(k)`. So every `|In(σ_k)| = 1`: `σ_k` is a singleton slot. ∎

**Equality [Lean `Parity.gt_eq`].** Split the tuples by whether `Miss = ∅`, with `Bad_k = {S_0(k,0), S_0(k,1)}`,
`Bad′_k = {S_1(k,0), S_1(k,1)}`, `φ_k = τ_k`. Since `τ_j(S_0(k, c)) = S_1(k, c ⊕ [k = j])`, (H1) holds. For (H2),
`B ∈ 𝓗_0` means `B = S_0(m, 1)`; if `B ∉ Bad_k` then `m ≠ k` and `τ_k B = S_1(m, 1) ∈ 𝓗_1`; conversely
`τ_k B = S_1(m, 1)` gives `B = S_0(m, 1 ⊕ [m = k])`, and `m = k` would put `B` in `Bad_k`. Lemma 1 equates the
`Miss ≠ ∅` parts. If `Miss(A) = ∅`, every `k` is hit, so by rigidity `A_{f(k)} = S_0(k, c_k)` for some `f`;
`f` is injective (the sets `S_0(k, c)` are distinct for distinct `k`), so `A = (S_0(π i, c_i))_i` with `π` a
permutation, and conversely every such pattern has `Miss = ∅`. Map it to `(S_1(π i, c_i))_i`. Slot statistics
agree: singletons have size `2^{t−2}` and lie in `𝓗` iff `c_i = 1`; pair intersections and unions have sizes
`2^{t−3}` and `3·2^{t−3}` (`π i ≠ π j`) and are not in `𝓗` (wrong size). Hence `T^(t)(E_0) = T^(t)(E_1)`.

**Separation [Lean `Parity.gt_ne`].** On `E_0` take `A₀ = (S_0(0,1), …, S_0(t−1,1), {0})`. A tuple on `E_1`
with its profile has, for `k < t`, `|A_k| = r` and rank `r − 1`, so `A_k = S_1(f(k), 1)`; the intersections of
size `2^{t−3} ≠ 2^{t−2}` force `f` injective, hence onto. `A_t` has one element `x`; `x` is odd, so `x_{k₀} = 1`
for some `k₀ = f(k)`, and `x ∈ A_k ∩ A_t`, whereas `S_0(k,1) ∩ {0} = ∅`. Lemma 2 gives
`T^(t+1)(E_0) ≠ T^(t+1)(E_1)`. With §3.4 this proves the theorem for all `g ≥ 4` [`Parity.conj_ge_four`].

### 3.6 Genus g = 1, 2, 3 [Lean `LowGenus`, `Low1`, `Low2`, `Low3`]

All are rank-3 gadgets whose circuit-hyperplanes are 3-sets meeting in at most one element.

**Chain lemma [Lean `miss_nonempty_of_chains`].** For `h ≤ 3`, `Slot h` is covered by `h` chains of the
pointwise order of the Boolean slot functions (for `h = 3`: `a₀∧a₁ ≤ a₀ ≤ a₀∨a₂`, `a₁∧a₂ ≤ a₁ ≤ a₀∨a₁`,
`a₀∧a₂ ≤ a₂ ≤ a₁∨a₂`; checked by `decide`). Slots in one chain have comparable slot sets for every tuple. If
`Bad_0, …, Bad_h` are pairwise disjoint families of 3-sets and `Miss(A) = ∅`, the `h + 1` hitting slots give
distinct 3-sets, two of which lie in one chain (pigeonhole), hence are comparable, hence equal: impossible.
So with `h + 1` such families, `Miss ≠ ∅` for every `h`-tuple and Lemma 1 equates the whole sums (`φ_k` maps
`E` to itself; `Bad′ = Bad`).

- **g = 1** (six elements). `𝓗_X = {012, 345}`, `𝓗_Y = {012, 234}`; `φ = (id, (2 5))`,
  `Bad = ({345, 234}, {012, 015})`. Separation at genus 2: `(012, 345)` has disjoint circuit-hyperplane
  probes; the two members of `𝓗_Y` meet.
- **g = 2, 3** (`m = g + 1`, `2m`-cycle). Elements `c_i = i`, `d_i = 2m + i` (`i < 2m`),
  `T_i = {c_i, d_i, c_{i+1}}` (indices mod `2m`). `X` is the loose `2m`-cycle `{T_i}`. For `k < m` let
  `T′_k = {c_k, d_k, c_{k+m+1}}`, `T′_{k+m} = {c_{k+m}, d_{k+m}, c_{k+1}}`; replacing `T_k, T_{k+m}` by
  `T′_k, T′_{k+m}` cuts the cycle into two loose `m`-cycles. `Y` is the cut at `k = m − 1`;
  `Bad_k = {T_k, T_{k+m}, T′_k, T′_{k+m}}` (pairwise disjoint families of 3-sets);
  `φ_k = Π_{k<j≤m−1} (c_j c_{j+m})(d_j d_{j+m})` (found by `scripts/find_cut_isos.py`). Idea: `X` and the cut at
  `k` have the same 3-sets outside `Bad_k`, and `φ_k` is an isomorphism from the cut at `k` onto `Y` (by
  construction in the search). What Lean checks (`e1`–`e6`, by `decide` over indices) is exactly what (H1),
  (H2) and the chain lemma need: `φ_j` maps every `Bad_k` onto itself, `φ_k` maps `𝓗_X ∖ Bad_k` onto
  `𝓗_Y ∖ Bad_k`, and the families `Bad_k` are disjoint families of 3-sets (`low_eq_idx`). Separation at genus `g + 1`: `Y` contains the cyclic tuple `(T_0, …, T_{m−2}, T′_{m−1})`
  (a triangle for `m = 3`, an induced 4-cycle for `m = 4` in the intersection pattern); a tuple on `X` with the
  same profile would be `m` circuit-hyperplanes of the loose `2m`-cycle with that pattern, which do not exist
  (`decide` over indices).

With §3.4 this gives the theorem for `g = 1, 2, 3` [`Low1.conj_one`, `Low2.conj_two`, `Low3.conj_three`]. ∎

*These are the source's own examples.*
- The `g = 1` pair is the source's `(R_6, Q_6)` (§4.1, `n = 3`). `R_{2n}` removes the two disjoint bases
  `X_1, X_2` from `U_{n,2n}`, and `Q_{2n}` removes `X_1, X_3` with `|X_1 ∩ X_3| = 1`. The source proves
  `T^(1)(R_{2n}) = T^(1)(Q_{2n})` and `T^(2)(R_{2n}) ≠ T^(2)(Q_{2n})` for every `n ≥ 3` (Propositions 4.3,
  4.4). So the case `g = 1` of the conjecture is already in the source, with the natural infinite sequence
  `(R_{2n}, Q_{2n})_{n ≥ 3}`.
- For `g = 2, 3`, `X` and `Y` are exactly the source's `S′_{4n}` and `S_{4n}` (Definition 4.6) with
  `n = m = 3, 4`, under the relabelling `c_i ↦ 2i`, `d_i ↦ 2i + 1`.
  - `S′_{4n}` removes the loose `2n`-cycle `F_3 ∪ F_4` from the bases of `U_{3,4n}`.
  - `S_{4n}` removes the two loose `n`-cycles `F_1 ∪ F_2`.
  - What is new for these `g` is the analysis. The source's equality theorem (Theorem 4.13) needs `n > g²`,
    whereas here equality holds at `g = n − 1`. Separation comes at genus `n` from singleton probes, where
    the source's Theorem 4.19 uses intersection covers of `C_n`, and those need at least 4 sets.

## 4. Sanity checks [Lean `GTMain`, `GTSanity`]

- `genusTutte_one`: `T^(1)(M)` is the Tutte polynomial `T(M; x, y)` of p. 3 (renamed to the slot variables).
- `specialization`: for every `g` and `M`, setting **every** variable of a slot involving `A_{g+1}` to 2 sends
  `T^(g+1)(M)` to `2^{|E|} T^(g)(M)`. This is the source's identity on p. 4 with a corrected substitution.
- `printed_identity_false`: the substitution as printed (`x_{A_{g+1}} = y_{A_{g+1}} = 2`, `x_{A_j∩A_{g+1}} = 2`,
  `y_{A_k∪A_{g+1}} = 2`, leaving `y_{A_j∩A_{g+1}}` and `x_{A_k∪A_{g+1}}` free) fails for `g = 1` and one loop: at
  the point where the free variables are 3 the two sides are 8 and 6. This is a misprint in the source and does
  not affect Conjecture 5.12.

## 5. Relation to the source and to the proof candidate

**What the source already gives.**
- The source's Theorem 4.22 (loose cycles and cover numbers) states separation of `T^(g)` from
  `T^(⌈√2 g⌉)`. Since `⌈√2⌉ = 2` and `⌈2√2⌉ = 3`, its statement already gives one-step separation for
  `g = 1, 2`. From `g = 3` on it does not (`⌈3√2⌉ = 5`).
- For `g = 1`, the source also proves the case outright in §4.1 (see §3.6).
- For `g = 2`, the printed proof of Theorem 4.22 ("clear from Theorem 4.19, Theorem 4.20, and Proposition
  4.21") does not reach it. Separation through Theorem 4.19 happens at genus `ι(C_n)`, and `ι(C_n) ≥ 4` for
  every `n ≥ 3`: three sets have at most three pairwise intersections, and `C_3` has no 2-fold intersecting
  cover by three sets. The source's own list uses four sets for `C_3`.
- Our `g = 2` case does not use Theorem 4.22.

**A remark on the source's Proposition 4.14.** Proposition 4.14 states that `T^(g)(S_{4n}) = T^(g)(S′_{4n})`
whenever `g ≤ ⌈(5 + √(8n − 15))/2⌉`. For `n = 3` the bound is 4, and for `n = 4` it is 5. The bound in the
proof, `binom(g−2, 2) + 2 ≥ n`, is strictly smaller, but it still covers genus 3 for `n = 3` and genus 4 for
`n = 4`. The Lean theorems `Low2.gt_ne` and `Low3.gt_ne` show the opposite: `T^(3)(S_12) ≠ T^(3)(S′_12)`
and `T^(4)(S_16) ≠ T^(4)(S′_16)`. The witness is a loose `n`-cycle of `S_{4n}` placed in the `n` singleton
slots, which `S′_{4n}` cannot match. An independent count in the final check found 12 such tuples against 0
for `n = 3`, and 16 against 0 for `n = 4`. So Proposition 4.14 fails for `n = 3, 4`, and by the same
singleton argument, not machine-checked, also for `n = 5`. Lemma 4.16, which it rests on, assumes
`n ≥ 4`. The equality half of Theorem 4.22 goes through Proposition 4.21, which uses the bound of
Proposition 4.14, so the source's proof of Theorem 4.22 is unreliable at least for small `g`. None of this
touches Conjecture 5.12 or our proof, which uses no result of the source.

**What is new.**
- One-step separation for every `g`.
- In particular `g ≥ 4`, by the parity gadget and the rigidity lemma: the source's loose-cycle family
  cannot give one step there.
- For `g = 2, 3`, the sharp equality analysis of the source's own pair at `n = g + 1`.

The formal proof follows the candidate's
constructions (PROOF-361823 §§4–6) but replaces its expansion (2)–(3) and constrained-sum transport by the
bijection of Lemma 1, as the review suggested. It also proves rigidity in the private-input form and handles
`g = 2, 3` by the cut involutions `φ_k` and the chain lemma instead of incidence-type counts. Finally, it uses
an explicit `g = 1` bijection.

## 6. Significance

This settles, in the affirmative and for every `g`, a conjecture posed in an arXiv preprint (2024, v1, no
journal version) on a recently introduced invariant. The proof is elementary: sparse paving matroids, a
parity construction reminiscent of Cai–Fürer–Immerman gadgets, and a short combinatorial rigidity argument.
The pre-Lean reviewer (Claude Opus 5.5) estimated a 0.70 probability that a specialist would call it not
routine.

The result is modest in several respects:
- The cases `g = 1, 2, 3` use the source's own matroids. The case `g = 1` is the source's §4.1, and
  `g = 2, 3` use its `S_{4n}, S′_{4n}` at `n = 3, 4`.
- The genuinely new construction is for `g ≥ 4`.
- For reading (R1), the sequences for each `g` are one pair padded by loops. For reading (R2), the family
  is one explicit pair per `g`.
- The matroids are not claimed to be representable, graphic, connected or simple.

One observation puts the statement in perspective. Any two non-isomorphic matroids with the same Tutte
polynomial first differ at some genus `h ≥ 2`, and they then give one-step separation at `g = h − 1`. The
content of the conjecture is therefore that **every** `g` occurs. Nothing in the source controls the first
separating genus of its families finely enough to hit every `g`.

The contribution is a complete, machine-checked answer to the question as posed, with a gap of one genus
where the source's Theorem 4.22 states a factor `√2`. Under reading (R2) this also answers Problem 5.11 with
`c1 = 1`, which is optimal. By the specialization identity (Lean `specialization`), equality at genus `g`
forces equality at every lower genus. A separating genus `⌈c1 g + c2⌉` must therefore exceed `g` for every
`g`, which is impossible when `c1 < 1`. The result says nothing about Problem 5.9 (graphic matroids).

## 7. Prior art (from the review, lane X40, §1)

- arXiv:2402.06845 (abs page re-fetched 2026-11-20) lists only v1 (10 Feb 2024) and no journal reference.
- OpenAlex lists no genuine citing work; its "citing" list for this work contains only older papers (an
  index artefact).
- Wakefield, *Chain Tutte polynomials* (EJC 33(2) 2026, P2.21) mentions genus-g polynomials only as complete
  invariants.
- Goodall–Jouve–Sereni arXiv:2510.05658 is unrelated (irreducibility and monodromy).
- The proof lane's bounded reading of Shnoudi's paper on genus separation for Type II codes of length 24 found
  no matroid statement.
- The omega registry (issues and PRs for "2402.06845", "Tutte polynomial genus", "Miezaki Oura Sakuma"), the
  Principia ids and clone, and web searches gave no hit.

Refreshed by the final check on 2026-11-20:
- The arXiv abs page shows v1 only, with no journal reference.
- OpenAlex `cites:W4391800542` returns only the authors' own earlier papers: Proc. Japan Acad. 2019, and
  Graphs Combin. 2020.
- Semantic Scholar refused with HTTP 429, and the arXiv API with "Rate exceeded". Neither was retried
  beyond once.
- Web searches for "Tutte polynomials of genus" and "genus g Tutte polynomial" found only the source, its
  announcement and machine summaries.
- The omega registry `the-omega-institute/trureturing`: issue searches for "2402.06845", "Tutte genus
  Miezaki", "separation genus Tutte polynomial" and "361823", and a PR search for "2402.06845". No hits.
- The ReuF2F benchmark `cmu-l3/reuF2F` (created 2026-10-18, last pushed 2026-10-25): its 244 metadata rows
  and file tree contain no entry for this source, Miezaki, or genus Tutte polynomials. Its only matroid
  entry is an unrelated conjecture of Dochtermann et al.
- Principia: neither 361823 nor 361822 (the other MathDB record from this source, Conjecture 5.7) is in the
  id list or the clone.
- The mio-qwq and openai/math clones: no hit for the arXiv id or the key terms.

As far as these searches go, the result is not public. This is a bounded search, not an exhaustive
literature review.

## 8. Lean map

| Step | Declaration | Module |
|---|---|---|
| Definition 1.3 | `Slot`, `slotSet`, `genusTutte`, `MiezakiConj512` | GTDefs |
| §3.1 matroid and rank | `SP.matroid`, `SP.eRk_eq`, `SP.genusTutte_eq` | GTSparse |
| Lemma 1, Lemma 2 | `sum_miss_eq`, `gt_ne_of_witness` | GTTransfer |
| §3.4 | `gt_equiv`, `gt_sum`, `gt_loops_ne_zero`, `Gadget.genusTutte_pad`, `conj_of_gadgets` | GTPad |
| parity counts, surjectivity | `card_S`, `card_S_inter`, `card_S_union`, `proj3`, `gadget` | Parity |
| rigidity | `card_le_one_of_private`, `Parity.rigidity` | Rigidity |
| g ≥ 4 | `Parity.gt_eq`, `Parity.gt_ne`, `Parity.conj_ge_four` | ParityGenus |
| chain lemma, low equality | `miss_nonempty_of_chains`, `ch1/2/3_spec`, `low_eq`, `low_eq_idx` | LowGenus |
| g = 1, 2, 3 | `Low1.conj_one`, `Low2.conj_two`, `Low3.conj_three` | Low1–3 |
| endpoint, sanity | `miezaki_conj_5_12`, `genusTutte_one`, `specialization` | GTMain |
| misprint | `Sanity.printed_identity_false` | GTSanity |

13 modules, 2,349 lines.

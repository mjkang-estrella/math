# LEAN-SOURCE-APPENDIX: MathDB 368177 (Burmester–Kühn, arXiv:2504.19661, Conjecture A.7)

All 23 modules in import order, byte-identical to `src/` (each file ends with a single newline). Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json). Main endpoints: `TSI.tsi_i` (TsiMainI), `TSI.tsi_ii` (TsiMainII), `TSI.conjecture_A7` and `TSI.tsi_ii_tau_nil_false_uri` (TsiEnd), `TSI.tsi_ii_tau_nil_false`, `TSI.example_A6_i` and `TSI.example_A6_ii` (TsiExamples).

### `TsiDefs.lean`

```lean
import Mathlib.NumberTheory.Bernoulli

/-!
# Literal definitions for Burmester–Kühn, arXiv:2504.19661, Def. 5.1, (44), Def. 5.3, (55), Def. A.5

Indices (compositions) are lists of integers; the endpoints assume every letter is positive.
The inserted letter `|σ₂| - d₁` of Def. A.5 is an integer and is placed literally; a term whose
inserted letter is `≤ 0` vanishes because its companion factor `μ_{≤ 0, ·}` is `0`.
-/

namespace TSI

open Finset

/-- Def. 5.1: `ind_a(α) = min_{1 ≤ j ≤ s} {j | α₁ + ⋯ + α_j ≥ a}`, and `0` if `α = ∅` or `a > |α|`. -/
noncomputable def ind (a : ℤ) (α : List ℤ) : ℕ :=
  if h : α ≠ [] ∧ a ≤ α.sum then
    Nat.find (p := fun j => 1 ≤ j ∧ j ≤ α.length ∧ a ≤ (α.take j).sum)
      ⟨α.length, Nat.one_le_iff_ne_zero.mpr (by simpa using h.1), le_rfl, by simpa using h.2⟩
  else 0

/-- (44): `B₁(m,n) = (1/m!) ∑_{k=0}^{n-1} C(m,k) B_k` with Mathlib's `bernoulli` (`B₁ = -1/2`). -/
noncomputable def B1 (m n : ℕ) : ℚ :=
  (1 / (m.factorial : ℚ)) * ∑ k ∈ range n, (m.choose k : ℚ) * bernoulli k

/-- (55): the multiplicity attached to a coefficient array `B`; `0` if `ind = 0`.
The source defines it for thresholds `a ∈ ℕ`; a threshold `a ≤ 0` gives `0`. -/
noncomputable def muB (B : ℕ → ℕ → ℚ) (a : ℤ) (α : List ℤ) : ℚ :=
  if a ≤ 0 then 0 else if ind a α = 0 then 0 else B α.length (ind a α)

/-- Def. 5.3: the uri multiplicities. -/
noncomputable def mu (a : ℤ) (α : List ℤ) : ℚ := muB B1 a α

/-- Formal ℤ-linear sums of indices. -/
abbrev FSum := List (ℤ × List ℤ)

/-- A single index as a formal sum. -/
def idx (w : List ℤ) : FSum := [(1, w)]

/-- Auxiliary for `shuffle`: `shuffleCons x u (shuffle u) v = shuffle (x :: u) v`. -/
def shuffleCons (x : ℤ) (u : List ℤ) (shu : List ℤ → List (List ℤ)) : List ℤ → List (List ℤ)
  | [] => [x :: u]
  | y :: v => (shu (y :: v)).map (x :: ·) ++ (shuffleCons x u shu v).map (y :: ·)

/-- The shuffle product of two indices, with multiplicity, by the recursion (19):
`1 ⧢ A = A = A ⧢ 1`, `xA ⧢ yB = x(A ⧢ yB) + y(xA ⧢ B)`. -/
def shuffle : List ℤ → List ℤ → List (List ℤ)
  | [], v => [v]
  | x :: u, v => shuffleCons x u (shuffle u) v

/-- Bilinear extension of the shuffle product to formal sums. -/
def shuffleF (A C : FSum) : FSum :=
  A.flatMap fun p => C.flatMap fun q => (shuffle p.2 q.2).map fun w => (p.1 * q.1, w)

/-- Bilinear extension of concatenation `(k, l)` to formal sums. -/
def catF (A C : FSum) : FSum :=
  A.flatMap fun p => C.map fun q => (p.1 * q.1, p.2 ++ q.2)

/-- The reversed index `k̄ = (-1)^d (k_d, …, k_1)`. -/
def revF (k : List ℤ) : FSum := [((-1) ^ k.length, k.reverse)]

/-- Linear extension of `μ^B_{a,·}` to formal sums. -/
noncomputable def muF (B : ℕ → ℕ → ℚ) (a : ℤ) (A : FSum) : ℚ :=
  (A.map fun p => (p.1 : ℚ) * muB B a p.2).sum

/-- Def. A.5 (i) for the multiplicity `μ^B`, at given `σ, ϑ, d₁, d₂`.  The decompositions
`(σ₁, σ₂) = σ` are `(σ.take i, σ.drop i)` for `0 ≤ i ≤ ℓ(σ)`. -/
def TSI_i (B : ℕ → ℕ → ℚ) (σ ϑ : List ℤ) (d₁ d₂ : ℕ) : Prop :=
  muF B (σ.sum + ϑ.sum - d₁ - d₂) (shuffleF (idx σ) (idx ϑ)) =
    ∑ i ∈ range (σ.length + 1), ∑ j ∈ range (ϑ.length + 1),
      (muF B ((σ.drop i).sum - d₁) (idx (σ.drop i)) *
          muF B (σ.sum + ϑ.sum - d₁ - d₂)
            (catF (catF (shuffleF (idx (σ.take i)) (idx (ϑ.take j)))
              (idx [(σ.drop i).sum - d₁])) (idx (ϑ.drop j))) +
        muF B ((ϑ.drop j).sum - d₂) (idx (ϑ.drop j)) *
          muF B (σ.sum + ϑ.sum - d₁ - d₂)
            (catF (catF (shuffleF (idx (σ.take i)) (idx (ϑ.take j)))
              (idx [(ϑ.drop j).sum - d₂])) (idx (σ.drop i))))

/-- Def. A.5 (ii) for the multiplicity `μ^B`, at given `σ, τ, ϑ, d₁, d₂`. -/
def TSI_ii (B : ℕ → ℕ → ℚ) (σ τ ϑ : List ℤ) (d₁ d₂ : ℕ) : Prop :=
  0 = ∑ i ∈ range (σ.length + 1), ∑ k ∈ range (τ.length + 1), ∑ j ∈ range (ϑ.length + 1),
    (muF B ((σ.drop i).sum + (τ.take k).sum - d₁)
          (shuffleF (idx (σ.drop i)) (revF (τ.take k))) *
        muF B (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
          (catF (catF (shuffleF (idx (σ.take i)) (revF (ϑ.drop j)))
              (idx [(σ.drop i).sum + (τ.take k).sum - d₁]))
            (shuffleF (idx (τ.drop k)) (revF (ϑ.take j)))) +
      muF B ((τ.drop k).sum + (ϑ.take j).sum - d₂)
          (shuffleF (idx (τ.drop k)) (revF (ϑ.take j))) *
        muF B (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
          (catF (catF (shuffleF (idx (σ.take i)) (revF (ϑ.drop j)))
              (idx [(τ.drop k).sum + (ϑ.take j).sum - d₂]))
            (shuffleF (idx (σ.drop i)) (revF (τ.take k)))))

/-- An index is a composition: every letter is a positive integer. -/
def IsComp (w : List ℤ) : Prop := ∀ x ∈ w, 0 < x

end TSI
```

### `TsiInd.lean`

```lean
import TsiDefs

/-! Computation rule for the threshold indicator `ind`. -/

namespace TSI

/-- Scan for the first prefix whose sum reaches `a`. -/
def firstIdx (a : ℤ) : List ℤ → ℕ
  | [] => 0
  | x :: r => if a ≤ x then 1 else firstIdx (a - x) r + 1

theorem firstIdx_spec : ∀ (α : List ℤ) (a : ℤ) (j : ℕ),
    (1 ≤ j ∧ j ≤ α.length ∧ a ≤ (α.take j).sum) →
    (1 ≤ firstIdx a α ∧ firstIdx a α ≤ α.length ∧ a ≤ (α.take (firstIdx a α)).sum) ∧
      ∀ m < firstIdx a α, ¬ (1 ≤ m ∧ m ≤ α.length ∧ a ≤ (α.take m).sum)
  | [], a, j, h => by simp at h; omega
  | x :: r, a, j, h => by
    by_cases hx : a ≤ x
    · simp only [firstIdx, hx, ite_true]
      refine ⟨⟨le_rfl, by simp, by simpa using hx⟩, fun m hm => ?_⟩
      omega
    · simp only [firstIdx, hx, ite_false]
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : 1 ≤ j' := by
        rcases Nat.eq_zero_or_pos j' with h0 | h0
        · subst h0; simp at h3; exact absurd h3 hx
        · exact h0
      simp only [List.take_succ_cons, List.sum_cons, List.length_cons] at h2 h3
      obtain ⟨⟨k1, k2, k3⟩, kmin⟩ := firstIdx_spec r (a - x) j' ⟨hj', by omega, by linarith⟩
      refine ⟨⟨by omega, by simp; omega, ?_⟩, fun m hm => ?_⟩
      · simp only [List.take_succ_cons, List.sum_cons]; linarith
      · rintro ⟨m1, m2, m3⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [List.take_succ_cons, List.sum_cons, List.length_cons] at m2 m3
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · subst h0; simp at m3; exact hx m3
        · exact kmin m' (by omega) ⟨h0, by omega, by linarith⟩

theorem ind_eq (a : ℤ) (α : List ℤ) :
    ind a α = if α ≠ [] ∧ a ≤ α.sum then firstIdx a α else 0 := by
  unfold ind
  split_ifs with h
  · rw [Nat.find_eq_iff]
    exact firstIdx_spec α a α.length
      ⟨Nat.one_le_iff_ne_zero.mpr (by simpa using h.1), le_rfl, by simpa using h.2⟩
  · rfl

end TSI
```

### `TsiExamples.lean`

```lean
import TsiInd

namespace TSI

/-- Example A.6 (i) of the source, for every coefficient array `B`. -/
theorem example_A6_i (B : ℕ → ℕ → ℚ) :
    TSI_i B [1, 2] [4, 3] 2 4 ↔
      B 4 3 + 2 * B 4 2 + 3 * B 4 1 = (2 * B 3 1 + 3 * B 3 2 + B 3 3) * B 2 1 := by
  simp only [TSI_i, muF, shuffleF, catF, idx, shuffle, shuffleCons, muB, ind_eq, firstIdx,
    Finset.sum_range_succ, Finset.sum_range_zero, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.sum_cons, List.sum_nil, List.take, List.drop, List.length_cons, List.length_nil]
  norm_num
  constructor <;> intro h <;> linear_combination h

end TSI

namespace TSI

/-- Example A.6 (ii) of the source, for every coefficient array `B` with the normalisation
`B(1,1) = 1` of (55) (the computed relation is `… - 15 B(6,6) B(1,1)`). -/
theorem example_A6_ii (B : ℕ → ℕ → ℚ) (hB : B 1 1 = 1) :
    TSI_ii B [2, 1] [4, 3] [5, 6] 1 2 ↔
      0 = 6 * B 4 4 * B 3 2 + 9 * B 3 3 * B 4 3 + 21 * B 4 4 * B 3 3 - 15 * B 6 6 := by
  simp only [TSI_ii, muF, shuffleF, catF, idx, revF, shuffle, shuffleCons, muB, ind_eq, firstIdx,
    Finset.sum_range_succ, Finset.sum_range_zero, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.sum_cons, List.sum_nil, List.take, List.drop, List.length_cons, List.length_nil,
    List.reverse_cons, List.reverse_nil]
  norm_num
  constructor <;> intro h
  · linear_combination h - 15 * B 6 6 * hB
  · linear_combination h + 15 * B 6 6 * hB

/-- Literal Def. A.5 (ii) with `τ = ∅` fails for every `B` with `B(1,1) = 1` (the normalisation
of (55)): `σ = τ = ∅`, `ϑ = (1)`, `d₁ = d₂ = 0` gives `0 = -1`. -/
theorem tsi_ii_tau_nil_false (B : ℕ → ℕ → ℚ) (hB : B 1 1 = 1) : ¬ TSI_ii B [] [] [1] 0 0 := by
  simp only [TSI_ii, muF, shuffleF, catF, idx, revF, shuffle, muB, ind_eq, firstIdx,
    Finset.sum_range_succ, Finset.sum_range_zero, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.sum_cons, List.sum_nil, List.take, List.drop, List.length_cons, List.length_nil,
    List.reverse_cons, List.reverse_nil]
  norm_num [hB]

/-- In particular for the uri multiplicities (`B₁(1,1) = 1`). -/
theorem B1_one_one : B1 1 1 = 1 := by simp [B1]

end TSI
```

### `TsiShuffle.lean`

```lean
import TsiDefs

/-! # Split sums and shuffle sums on words

`ss H w = ∑_{w = a b} H a b` (deconcatenation) and `Sh f u v = ∑_{w ∈ u ⧢ v} f w`.
The main result is `Sh_ss` (shuffles are compatible with deconcatenation). -/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace TSI

open Finset

/-- Sum over the decompositions `w = (a, b)`. -/
def ss (H : List ℤ → List ℤ → ℚ) (w : List ℤ) : ℚ :=
  ∑ i ∈ range (w.length + 1), H (w.take i) (w.drop i)

/-- Sum over the shuffles of `u` and `v`, with multiplicity. -/
def Sh (f : List ℤ → ℚ) (u v : List ℤ) : ℚ := ((shuffle u v).map f).sum

theorem shuffle_nil_left (v : List ℤ) : shuffle [] v = [v] := rfl

theorem shuffle_nil_right (u : List ℤ) : shuffle u [] = [u] := by cases u <;> rfl

theorem shuffle_cons_cons (x : ℤ) (u : List ℤ) (y : ℤ) (v : List ℤ) :
    shuffle (x :: u) (y :: v) =
      (shuffle u (y :: v)).map (x :: ·) ++ (shuffle (x :: u) v).map (y :: ·) := rfl

/-! ## Split sums -/

theorem ss_nil (H : List ℤ → List ℤ → ℚ) : ss H [] = H [] [] := by simp [ss]

theorem ss_cons (H : List ℤ → List ℤ → ℚ) (x : ℤ) (w : List ℤ) :
    ss H (x :: w) = H [] (x :: w) + ss (fun a b => H (x :: a) b) w := by
  unfold ss
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  simp

theorem ss_congr {H H' : List ℤ → List ℤ → ℚ} {w : List ℤ}
    (h : ∀ a b, a ++ b = w → H a b = H' a b) : ss H w = ss H' w :=
  Finset.sum_congr rfl fun i _ => h _ _ (List.take_append_drop i w)

theorem ss_ext {H H' : List ℤ → List ℤ → ℚ} (w : List ℤ) (h : ∀ a b, H a b = H' a b) :
    ss H w = ss H' w := ss_congr fun a b _ => h a b

theorem ss_add (H H' : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => H a b + H' a b) w = ss H w + ss H' w := Finset.sum_add_distrib

theorem ss_sub (H H' : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => H a b - H' a b) w = ss H w - ss H' w := Finset.sum_sub_distrib _ _

theorem ss_neg (H : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => - H a b) w = - ss H w := by simp [ss]

theorem ss_mul_left (c : ℚ) (H : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    c * ss H w = ss (fun a b => c * H a b) w := Finset.mul_sum _ _ _

theorem ss_mul_right (c : ℚ) (H : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss H w * c = ss (fun a b => H a b * c) w := Finset.sum_mul _ _ _

theorem ss_zero (w : List ℤ) : ss (fun _ _ => 0) w = 0 := by simp [ss]

theorem ss_comm (G : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (u v : List ℤ) :
    ss (fun a b => ss (G a b) v) u = ss (fun c d => ss (fun a b => G a b c d) u) v :=
  Finset.sum_comm

theorem ss_sum {ι : Type*} (s : Finset ι) (H : ι → List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => ∑ i ∈ s, H i a b) w = ∑ i ∈ s, ss (H i) w := Finset.sum_comm

/-- Coassociativity of deconcatenation. -/
theorem ss_coassoc (F : List ℤ → List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => ss (F a) b) w = ss (fun x d => ss (fun a c => F a c d) x) w := by
  induction w generalizing F with
  | nil => simp [ss_nil]
  | cons x w ih =>
    rw [ss_cons, ss_cons, ih (fun a => F (x :: a)), ss_cons]
    simp only [ss_nil, ss_cons]
    rw [ss_add]
    ring

/-- Cutting a word that contains a marked letter `x`. -/
theorem ss_append_cons (H : List ℤ → List ℤ → ℚ) (w : List ℤ) (x : ℤ) (z : List ℤ) :
    ss H (w ++ x :: z) =
      ss (fun P Q => H P (Q ++ x :: z)) w + ss (fun P Q => H (w ++ x :: P) Q) z := by
  induction w generalizing H with
  | nil => simp [ss_nil, ss_cons]
  | cons y w ih =>
    rw [List.cons_append, ss_cons, ih, ss_cons]
    simp only [List.nil_append, List.cons_append]
    ring

theorem ss_len (h : ℕ → ℕ → ℚ) (w : List ℤ) :
    ss (fun a b => h a.length b.length) w = ∑ i ∈ range (w.length + 1), h i (w.length - i) := by
  unfold ss
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [List.length_take, List.length_drop]
  congr 1
  simp at hi; omega

theorem ss_reverse (H : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss H w.reverse = ss (fun a b => H b.reverse a.reverse) w := by
  unfold ss
  rw [List.length_reverse, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [List.take_reverse, List.drop_reverse]
  have e : w.length - (w.length + 1 - 1 - i) = i := by omega
  simp only [e]

theorem ss_first_nil (g : List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => if a.length = 0 then g b else 0) w = g w := by
  unfold ss
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    simp only [Finset.mem_range] at hi
    simp only [List.length_take]
    split_ifs with h
    · omega
    · rfl
  · simp

/-! ## Shuffle sums -/

theorem Sh_nil_left (f : List ℤ → ℚ) (v : List ℤ) : Sh f [] v = f v := by
  simp [Sh, shuffle_nil_left]

theorem Sh_nil_right (f : List ℤ → ℚ) (u : List ℤ) : Sh f u [] = f u := by
  simp [Sh, shuffle_nil_right]

theorem Sh_cons_cons (f : List ℤ → ℚ) (x : ℤ) (u : List ℤ) (y : ℤ) (v : List ℤ) :
    Sh f (x :: u) (y :: v) =
      Sh (fun w => f (x :: w)) u (y :: v) + Sh (fun w => f (y :: w)) (x :: u) v := by
  simp [Sh, shuffle_cons_cons, List.map_map, Function.comp_def]

theorem Sh_ext {f g : List ℤ → ℚ} (u v : List ℤ) (h : ∀ w, f w = g w) : Sh f u v = Sh g u v := by
  simp [Sh, funext h]

theorem Sh_congr {f g : List ℤ → ℚ} {u v : List ℤ} (h : ∀ w ∈ shuffle u v, f w = g w) :
    Sh f u v = Sh g u v := by
  unfold Sh; rw [List.map_congr_left h]

theorem Sh_add (f g : List ℤ → ℚ) (u v : List ℤ) :
    Sh (fun w => f w + g w) u v = Sh f u v + Sh g u v := by
  simp [Sh, List.sum_map_add]

theorem Sh_mul_left (c : ℚ) (f : List ℤ → ℚ) (u v : List ℤ) :
    Sh (fun w => c * f w) u v = c * Sh f u v := by
  simp [Sh, List.sum_map_mul_left]

theorem Sh_mul_right (c : ℚ) (f : List ℤ → ℚ) (u v : List ℤ) :
    Sh (fun w => f w * c) u v = Sh f u v * c := by
  simp [Sh, List.sum_map_mul_right]

theorem list_sum_map_finset_sum {ι : Type*} (s : Finset ι) (F : ι → List ℤ → ℚ) :
    ∀ L : List (List ℤ), (L.map fun w => ∑ i ∈ s, F i w).sum = ∑ i ∈ s, (L.map (F i)).sum
  | [] => by simp
  | w :: L => by
    simp only [List.map_cons, List.sum_cons, list_sum_map_finset_sum s F L]
    rw [Finset.sum_add_distrib]

theorem Sh_ss_comm (G : List ℤ → List ℤ → List ℤ → ℚ) (u v z : List ℤ) :
    Sh (fun w => ss (G w) z) u v = ss (fun a b => Sh (fun w => G w a b) u v) z := by
  unfold Sh ss
  exact list_sum_map_finset_sum _ _ _

theorem Sh_comm (f : List ℤ → ℚ) (u v : List ℤ) : Sh f u v = Sh f v u := by
  induction u generalizing v f with
  | nil => rw [Sh_nil_left, Sh_nil_right]
  | cons x u ihu =>
    induction v generalizing f with
    | nil => rw [Sh_nil_left, Sh_nil_right]
    | cons y v ihv =>
      rw [Sh_cons_cons, Sh_cons_cons, ihu, ihv, add_comm]

theorem perm_of_mem_shuffle : ∀ (u v w : List ℤ), w ∈ shuffle u v → w.Perm (u ++ v)
  | [], v, w, h => by simp [shuffle_nil_left] at h; simp [h]
  | x :: u, [], w, h => by simp [shuffle_nil_right] at h; simp [h]
  | x :: u, y :: v, w, h => by
    rw [shuffle_cons_cons, List.mem_append, List.mem_map, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · exact (perm_of_mem_shuffle u (y :: v) w' hw').cons x
    · exact ((perm_of_mem_shuffle (x :: u) v w' hw').cons y).trans List.perm_middle.symm

theorem length_shuffle : ∀ (u v : List ℤ),
    (shuffle u v).length = (u.length + v.length).choose u.length
  | [], v => by simp [shuffle_nil_left]
  | x :: u, [] => by simp [shuffle_nil_right]
  | x :: u, y :: v => by
    rw [shuffle_cons_cons, List.length_append, List.length_map, List.length_map,
      length_shuffle u (y :: v), length_shuffle (x :: u) v]
    simp only [List.length_cons]
    rw [show u.length + 1 + (v.length + 1) = (u.length + v.length + 1) + 1 by omega,
      Nat.choose_succ_succ]
    congr 2 <;> omega

/-- A shuffle sum of a function that is constant on the shuffles. -/
theorem Sh_const {f : List ℤ → ℚ} {u v : List ℤ} (c : ℚ)
    (h : ∀ w, w.Perm (u ++ v) → f w = c) :
    Sh f u v = ((u.length + v.length).choose u.length : ℚ) * c := by
  rw [Sh_congr (g := fun _ => c) (fun w hw => h w (perm_of_mem_shuffle u v w hw))]
  simp [Sh, length_shuffle]

/-- Lemma 2: shuffles are compatible with deconcatenation. -/
theorem Sh_ss (G : List ℤ → List ℤ → ℚ) (u v : List ℤ) :
    Sh (ss G) u v =
      ss (fun u₁ u₂ => ss (fun v₁ v₂ => Sh (fun P => Sh (G P) u₂ v₂) u₁ v₁) v) u := by
  induction u generalizing v G with
  | nil => simp [Sh_nil_left, ss_nil]
  | cons x u ihu =>
    induction v generalizing G with
    | nil => simp [Sh_nil_right, Sh_nil_left, ss_nil]
    | cons y v ihv =>
      have h1 : Sh (ss G) (x :: u) (y :: v) =
          Sh (G []) (x :: u) (y :: v) + Sh (ss fun a b => G (x :: a) b) u (y :: v) +
            Sh (ss fun a b => G (y :: a) b) (x :: u) v := by
        rw [Sh_cons_cons, Sh_cons_cons (G [])]
        simp only [ss_cons, Sh_add]
        ring
      rw [h1, ihu, ihv]
      simp only [ss_cons, ss_nil, Sh_nil_left, Sh_nil_right, Sh_cons_cons, Sh_add, ss_add]
      ring

end TSI
```

### `TsiBern.lean`

```lean
import Mathlib.NumberTheory.Bernoulli

/-! # Elementary Bernoulli and binomial identities -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- `b_k = B_k / k!`. -/
noncomputable def bb (k : ℕ) : ℚ := bernoulli k / k.factorial

/-- `1 / k!`. -/
noncomputable def ff (k : ℕ) : ℚ := 1 / k.factorial

theorem choose_mul_ff (a b : ℕ) : ((a + b).choose a : ℚ) * ff (a + b) = ff a * ff b := by
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [← Nat.choose_symm_add] at h
  have h' : ((a + b).choose a : ℚ) * a.factorial * b.factorial = (a + b).factorial := by
    exact_mod_cast h
  unfold ff
  have ha : (a.factorial : ℚ) ≠ 0 := by positivity
  have hb : (b.factorial : ℚ) ≠ 0 := by positivity
  have hab : ((a + b).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith [h']

/-- Lemma 3(a): `∑_{r+u=N} b_u/(r+1)! = δ_{N,0}`. -/
theorem bern_a (N : ℕ) :
    ∑ i ∈ range (N + 1), bb (N - i) * ff (i + 1) = if N = 0 then 1 else 0 := by
  have hs := sum_bernoulli (N + 1)
  have key : ∑ k ∈ range (N + 1), bb k * ff (N + 1 - k) =
      ff (N + 1) * ∑ k ∈ range (N + 1), ((N + 1).choose k : ℚ) * bernoulli k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    have hc := choose_mul_ff k (N + 1 - k)
    rw [show k + (N + 1 - k) = N + 1 by omega] at hc
    unfold bb
    have : bernoulli k / k.factorial * ff (N + 1 - k) = bernoulli k * (ff k * ff (N + 1 - k)) := by
      unfold ff; ring
    rw [this, ← hc]; ring
  rw [← Finset.sum_range_reflect]
  have e : ∑ j ∈ range (N + 1), bb (N - (N + 1 - 1 - j)) * ff (N + 1 - 1 - j + 1) =
      ∑ k ∈ range (N + 1), bb k * ff (N + 1 - k) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    congr 2 <;> omega
  rw [e, key, hs]
  by_cases hN : N = 0
  · subst hN; simp [ff]
  · simp [hN]

/-- Upper Vandermonde: `∑_{i ≤ M} C(r+i, r) C(T+M-i, T) = C(r+T+M+1, M)`. -/
theorem vand_upper (r : ℕ) : ∀ T M : ℕ,
    ∑ i ∈ range (M + 1), (r + i).choose r * (T + (M - i)).choose T = (r + T + M + 1).choose M := by
  intro T
  induction T with
  | zero =>
    intro M
    have h2 := Finset.sum_antidiagonal_choose_add r M
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ j => (r + j).choose r)] at h2
    simp only [Nat.choose_zero_right, mul_one, Nat.add_zero]
    rw [← Finset.sum_range_reflect] at h2
    have e : ∑ j ∈ range (M + 1), (r + (M - (M + 1 - 1 - j))).choose r =
        ∑ i ∈ range (M + 1), (r + i).choose r := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      congr 2; omega
    rw [e] at h2
    rw [h2, Nat.choose_symm_of_eq_add]; omega
  | succ T ih =>
    intro M
    induction M with
    | zero => simp
    | succ M ihM =>
      have step : ∀ i ∈ range (M + 1 + 1),
          (r + i).choose r * (T + 1 + (M + 1 - i)).choose (T + 1) =
            (r + i).choose r * (T + (M + 1 - i)).choose T +
              (if i ≤ M then (r + i).choose r * (T + 1 + (M - i)).choose (T + 1) else 0) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [show T + 1 + (M + 1 - i) = (T + (M + 1 - i)) + 1 by omega, Nat.choose_succ_succ',
          mul_add]
        congr 1
        split_ifs with h
        · congr 2; omega
        · rw [show i = M + 1 by omega]; simp
      rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ih (M + 1)]
      rw [← Finset.sum_filter, show (range (M + 1 + 1)).filter (· ≤ M) = range (M + 1) by
        ext i; simp; omega, ihM]
      rw [show r + (T + 1) + (M + 1) + 1 = (r + T + (M + 1) + 1) + 1 by omega,
        Nat.choose_succ_succ', add_comm]
      congr 2; omega

/-- Lemma 3(b): `∑_{i ≤ M} C(r+i,r) C(T+M-i,T) / (r+T+M+1)! = 1/((r+T+1)! M!)`. -/
theorem bern_b (r T M : ℕ) :
    ∑ i ∈ range (M + 1), ((r + i).choose r : ℚ) * ((T + (M - i)).choose T : ℚ) *
      ff (r + T + M + 1) = ff (r + T + 1) * ff M := by
  rw [← Finset.sum_mul]
  have h := vand_upper r T M
  have h' : ∑ i ∈ range (M + 1), ((r + i).choose r : ℚ) * ((T + (M - i)).choose T : ℚ) =
      ((r + T + M + 1).choose M : ℚ) := by exact_mod_cast h
  rw [h']
  have hc := choose_mul_ff M (r + T + 1)
  rw [show M + (r + T + 1) = r + T + M + 1 by omega] at hc
  rw [hc, mul_comm]

/-- `∑_{k ≤ p} (-1)^k / (k! (p-k)!) = 0` for `p ≥ 1`. -/
theorem alt_ff (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ range (p + 1), (-1 : ℚ) ^ k * ff k * ff (p - k) = 0 := by
  have h := add_pow (-1 : ℚ) 1 p
  rw [show (-1 : ℚ) + 1 = 0 by norm_num, zero_pow (by omega)] at h
  have : ∑ k ∈ range (p + 1), (-1 : ℚ) ^ k * ff k * ff (p - k) =
      ff p * ∑ k ∈ range (p + 1), (-1 : ℚ) ^ k * 1 ^ (p - k) * (p.choose k : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    have hc := choose_mul_ff k (p - k)
    rw [show k + (p - k) = p by omega] at hc
    rw [one_pow, mul_one, mul_assoc, ← hc]; ring
  rw [this, ← h, mul_zero]

end TSI
```

### `TsiPS.lean`

```lean
import TsiBern

/-! # Power-series identities for `β(x) = x/(eˣ-1)` at numeric scalings -/

set_option linter.unusedSimpArgs false

namespace TSI

open PowerSeries Finset

theorem coeff_resc_beta (a : ℚ) (n : ℕ) :
    coeff n (rescale a (bernoulliPowerSeries ℚ)) = a ^ n * bb n := by
  simp [coeff_rescale, bernoulliPowerSeries, bb]

theorem coeff_resc_exp (a : ℚ) (n : ℕ) : coeff n (rescale a (exp ℚ)) = a ^ n * ff n := by
  simp [coeff_rescale, coeff_exp, ff]

theorem beta_E (a : ℚ) :
    rescale a (bernoulliPowerSeries ℚ) * (rescale a (exp ℚ) - 1) = C a * X := by
  rw [← rescale_X, ← bernoulliPowerSeries_mul_exp_sub_one ℚ, map_mul, map_sub, map_one]

theorem E_ne_zero {a : ℚ} (ha : a ≠ 0) : rescale a (exp ℚ) - 1 ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp [coeff_resc_exp, ff] at this
  exact ha this

theorem CX_ne_zero {a : ℚ} (ha : a ≠ 0) : (C a * X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp at this
  exact ha this

/-- `G(P,Q) = (β(P+Q) - β(Q))/P` as an explicit series (in one variable, scaled). -/
noncomputable def G (P Q : ℚ) : PowerSeries ℚ :=
  mk fun w => bb (w + 1) * ∑ e ∈ range (w + 1), (P + Q) ^ e * Q ^ (w - e)

theorem G_spec (P Q : ℚ) :
    C P * X * G P Q = rescale (P + Q) (bernoulliPowerSeries ℚ) -
      rescale Q (bernoulliPowerSeries ℚ) := by
  ext n
  rcases n with _ | w
  · simp only [map_sub, coeff_resc_beta, mul_assoc, coeff_C_mul, coeff_zero_X_mul]; ring
  · rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, G, coeff_mk, map_sub, coeff_resc_beta,
      coeff_resc_beta]
    have hg := geom_sum₂_mul (P + Q) Q (w + 1)
    have e : ∑ i ∈ range (w + 1), (P + Q) ^ i * Q ^ (w + 1 - 1 - i) =
        ∑ e ∈ range (w + 1), (P + Q) ^ e * Q ^ (w - e) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
    rw [e, show P + Q - Q = P by ring] at hg
    rw [← sub_mul, ← hg]; ring

/-- Lemma 3(e) at a numeric scaling: `Φ(P,Q) = 0`. -/
theorem Phi_zero {P Q : ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : P + Q ≠ 0) :
    rescale P (bernoulliPowerSeries ℚ) * G P Q + rescale Q (bernoulliPowerSeries ℚ) * G Q P +
      rescale (P + Q) (bernoulliPowerSeries ℚ) = 0 := by
  set bP := rescale P (bernoulliPowerSeries ℚ)
  set bQ := rescale Q (bernoulliPowerSeries ℚ)
  set bPQ := rescale (P + Q) (bernoulliPowerSeries ℚ)
  set EP := rescale P (exp ℚ) - 1
  set EQ := rescale Q (exp ℚ) - 1
  set EPQ := rescale (P + Q) (exp ℚ) - 1
  have h1 : bP * EP = C P * X := beta_E P
  have h2 : bQ * EQ = C Q * X := beta_E Q
  have h3 : bPQ * EPQ = C (P + Q) * X := beta_E (P + Q)
  have g1 : C P * X * G P Q = bPQ - bQ := G_spec P Q
  have g2 : C Q * X * G Q P = bPQ - bP := by rw [G_spec Q P, add_comm Q P]
  have hx : (EP + 1) * (EQ + 1) = EPQ + 1 := by
    simp only [EP, EQ, EPQ, sub_add_cancel]; exact exp_mul_exp_eq_exp_add P Q
  have hC : (C (P + Q) : PowerSeries ℚ) = C P + C Q := map_add _ _ _
  have hK : (C P * X) * (C Q * X) * EP * EQ * EPQ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (CX_ne_zero hP) (CX_ne_zero hQ))
      (E_ne_zero hP)) (E_ne_zero hQ)) (E_ne_zero hPQ)
  have key : (bP * G P Q + bQ * G Q P + bPQ) * ((C P * X) * (C Q * X) * EP * EQ * EPQ) = 0 := by
    linear_combination (C P * X * G P Q) * (C Q * X * EQ * EPQ) * h1
      + (C P * X) * (C Q * X * EQ * EPQ) * g1
      + (C P * X) * (C Q * X) * EQ * h3 - (C P * X) * (C Q * X) * EPQ * h2
      + (C Q * X * G Q P) * (C P * X * EP * EPQ) * h2
      + (C Q * X) * (C P * X * EP * EPQ) * g2
      + (C Q * X) * (C P * X) * EP * h3 - (C Q * X) * (C P * X) * EPQ * h1
      + (C P * X) * (C Q * X) * EP * EQ * h3
      + (C P * X) * (C Q * X) * C (P + Q) * X * hx
      + (C P * X) * (C Q * X) * X * EPQ * hC
  exact (mul_eq_zero.mp key).resolve_right hK

/-- `E(a,c) = (e^{a} - e^{c})/(a-c)` as an explicit series. -/
noncomputable def Egen (a c : ℚ) : PowerSeries ℚ :=
  mk fun l => ff (l + 1) * ∑ e ∈ range (l + 1), a ^ e * c ^ (l - e)

theorem Egen_spec (a c : ℚ) : C (a - c) * X * Egen a c = rescale a (exp ℚ) - rescale c (exp ℚ) := by
  ext n
  rcases n with _ | w
  · simp only [map_sub, coeff_resc_exp, mul_assoc, coeff_C_mul, coeff_zero_X_mul]; simp [ff]
  · rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, Egen, coeff_mk, map_sub, coeff_resc_exp,
      coeff_resc_exp]
    have hg := geom_sum₂_mul a c (w + 1)
    have e : ∑ i ∈ range (w + 1), a ^ i * c ^ (w + 1 - 1 - i) =
        ∑ e ∈ range (w + 1), a ^ e * c ^ (w - e) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
    rw [e] at hg
    rw [← sub_mul, ← hg]; ring

/-- Lemma 3(c) at a numeric scaling: `β(a-c) E(a,c) = e^c`. -/
theorem cid {a c : ℚ} (h : a ≠ c) :
    rescale (a - c) (bernoulliPowerSeries ℚ) * Egen a c = rescale c (exp ℚ) := by
  have hac : a - c ≠ 0 := sub_ne_zero.mpr h
  have h1 := beta_E (a - c)
  have h2 := Egen_spec a c
  have hx := exp_mul_exp_eq_exp_add (A := ℚ) (a - c) c
  rw [sub_add_cancel] at hx
  have key : (rescale (a - c) (bernoulliPowerSeries ℚ) * Egen a c - rescale c (exp ℚ)) *
      (C (a - c) * X) = 0 := by
    linear_combination rescale (a - c) (bernoulliPowerSeries ℚ) * h2
      + rescale c (exp ℚ) * h1 - rescale (a - c) (bernoulliPowerSeries ℚ) * hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (CX_ne_zero hac))

end TSI
```

### `TsiCoeffC.lean`

```lean
import TsiPS
import Mathlib.Algebra.Polynomial.Roots

/-! # Lemma 3(c), 3(d) as coefficient identities -/

set_option linter.unusedSimpArgs false

namespace TSI

open PowerSeries Finset

/-- A polynomial vanishing at every integer `t ≥ 2` has zero coefficients. -/
theorem poly_vanish (N : ℕ) (g : ℕ → ℚ)
    (h : ∀ t : ℕ, 2 ≤ t → ∑ S ∈ range (N + 1), g S * (t : ℚ) ^ S = 0) :
    ∀ S ≤ N, g S = 0 := by
  set p : Polynomial ℚ := ∑ S ∈ range (N + 1), Polynomial.C (g S) * Polynomial.X ^ S with hpdef
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 2 : ℕ) : ℚ))
    · intro x y hxy
      have := Nat.cast_injective (R := ℚ) hxy
      omega
    · intro n
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hpdef, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact h (n + 2) (by omega)
  intro S hS
  have := congrArg (fun q => Polynomial.coeff q S) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  simpa [Finset.mem_range, Nat.lt_succ_of_le hS] using this

/-- Reindexing of a triple sum `(u, α, e) ↦ (α + e, e, u - α)`. -/
theorem reindex3 (N : ℕ) (F F' : ℕ → ℕ → ℕ → ℚ)
    (h : ∀ u α e, u ≤ N → α ≤ u → e ≤ N - u → F u α e = F' (α + e) e (u - α)) :
    ∑ u ∈ range (N + 1), ∑ α ∈ range (u + 1), ∑ e ∈ range (N - u + 1), F u α e =
      ∑ R ∈ range (N + 1), ∑ i ∈ range (R + 1), ∑ j ∈ range (N - R + 1), F' R i j := by
  simp only [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2.1 + x.2.2, x.2.2, x.1 - x.2.1⟩)
    (fun y _ => ⟨y.1 - y.2.1 + y.2.2, y.1 - y.2.1, y.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, α, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    obtain ⟨_, _, _⟩ := hx
    omega
  · rintro ⟨R, i, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    obtain ⟨_, _, _⟩ := hy
    omega
  · rintro ⟨u, α, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨_, _, _⟩ := hx
    dsimp only
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨R, i, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    obtain ⟨_, _, _⟩ := hy
    dsimp only
    simp only [show R - i + i = R by omega, show R - i + j - (R - i) = j by omega]
  · rintro ⟨u, α, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨_, _, _⟩ := hx
    exact h u α e (by omega) (by omega) (by omega)

/-- The coefficient array of Lemma 3(c). -/
noncomputable def cc (R S : ℕ) : ℚ :=
  ∑ i ∈ range (R + 1), ∑ j ∈ range (S + 1),
    (-1 : ℚ) ^ j * ((R - i + j).choose (R - i) : ℚ) * bb (R - i + j) * ff (i + (S - j) + 1)

theorem expand_c (a c : ℚ) (N : ℕ) :
    coeff N (rescale (a - c) (bernoulliPowerSeries ℚ) * Egen a c) =
      ∑ R ∈ range (N + 1), a ^ R * c ^ (N - R) * cc R (N - R) := by
  have hL : coeff N (rescale (a - c) (bernoulliPowerSeries ℚ) * Egen a c) =
      ∑ u ∈ range (N + 1), ∑ α ∈ range (u + 1), ∑ e ∈ range (N - u + 1),
        a ^ α * (-c) ^ (u - α) * (u.choose α : ℚ) * bb u * ff (N - u + 1) *
          (a ^ e * c ^ (N - u - e)) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [coeff_resc_beta, Egen, coeff_mk, sub_eq_add_neg, add_pow, Finset.sum_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hL]
  simp only [cc, Finset.mul_sum]
  refine reindex3 N _ _ fun u α e hu hα he => ?_
  have e1 : α + e - e = α := by omega
  have e2 : α + (u - α) = u := by omega
  have e3 : e + (N - (α + e) - (u - α)) + 1 = N - u + 1 := by omega
  rw [e1, e2, e3, neg_pow, show N - (α + e) = (u - α) + (N - u - e) by omega, pow_add, pow_add]
  ring

/-- Lemma 3(c): `∑_{α+r=R, β+T=S} (-1)^β C(α+β,α) b_{α+β}/(r+T+1)! = δ_{R,0}/S!`. -/
theorem bern_c (R S : ℕ) : cc R S = if R = 0 then ff S else 0 := by
  have key : ∀ N, ∀ S ≤ N, cc (N - S) S - (if S = N then ff N else 0) = 0 := by
    intro N
    apply poly_vanish N
    intro t ht
    have ht' : (1 : ℚ) ≠ t := by
      have : (2 : ℚ) ≤ t := by exact_mod_cast ht
      intro h; rw [← h] at this; norm_num at this
    have h1 := congrArg (coeff N) (cid ht')
    rw [expand_c, coeff_resc_exp] at h1
    simp only [one_pow, one_mul] at h1
    rw [← Finset.sum_range_reflect] at h1
    have e : ∑ j ∈ range (N + 1), (t : ℚ) ^ (N - (N + 1 - 1 - j)) * cc (N + 1 - 1 - j)
        (N - (N + 1 - 1 - j)) = ∑ S ∈ range (N + 1), cc (N - S) S * (t : ℚ) ^ S := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [show N - (N + 1 - 1 - j) = j by omega, show N + 1 - 1 - j = N - j by omega]
      ring
    rw [e] at h1
    simp only [sub_mul, Finset.sum_sub_distrib, h1, ite_mul, zero_mul]
    simp
    ring
  have := key (R + S) S (by omega)
  rw [show R + S - S = R by omega] at this
  by_cases hR : R = 0
  · subst hR; simp at this ⊢; linarith
  · simp only [eq_false (show ¬ (S = R + S) by omega), ite_false, sub_zero] at this
    simp only [this, eq_false hR, ite_false]

/-- The coefficient array of Lemma 3(d). -/
noncomputable def dd (R S : ℕ) : ℚ :=
  ∑ i ∈ range (R + 1), ∑ j ∈ range (S + 1),
    (-1 : ℚ) ^ i * ((R - i + (S - j)).choose (R - i) : ℚ) * bb (R - i + (S - j)) * ff (i + j + 1)

theorem neg_one_pow_sub (R i : ℕ) (h : i ≤ R) :
    (-1 : ℚ) ^ (R - i) = (-1) ^ R * (-1) ^ i := by
  have : (-1 : ℚ) ^ R = (-1) ^ (R - i) * (-1) ^ i := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- Lemma 3(d): `∑_{r'+α=R, s+β=S} (-1)^{r'} C(α+β,α) b_{α+β}/(r'+s+1)! = (-1)^R δ_{S,0}/R!`. -/
theorem bern_d (R S : ℕ) : dd R S = if S = 0 then (-1 : ℚ) ^ R * ff R else 0 := by
  have h : dd R S = (-1 : ℚ) ^ R * cc S R := by
    unfold dd cc
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [show R + 1 - 1 - i = R - i by omega, show R - (R - i) = i by omega,
      neg_one_pow_sub R i (by omega), Nat.choose_symm_add,
      show S - j + i = i + (S - j) by omega, show R - i + j + 1 = j + (R - i) + 1 by omega]
    ring
  rw [h, bern_c]
  split_ifs <;> ring

end TSI
```

### `TsiCoeffH.lean`

```lean
import TsiCoeffC

/-! # Lemma 3(e) in coefficient form: `H(A,m,B) = 0` (and `F(A,B) = H(A,0,B) = 0`) -/

set_option linter.unusedSimpArgs false

namespace TSI

open PowerSeries Finset

/-- Reindexing of a five-fold sum `(u, α, e, i, γ) ↦ (α+i, u-α+γ, i, u-α, e-i)`. -/
theorem reindex5 (N : ℕ) (F F' : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ)
    (h : ∀ u α e i γ, u ≤ N → α ≤ u → e ≤ N - u → i ≤ e → γ ≤ N - u - e →
      F u α e i γ = F' (α + i) (u - α + γ) i (u - α) (e - i)) :
    ∑ u ∈ range (N + 1), ∑ e ∈ range (N - u + 1), ∑ γ ∈ range (N - u - e + 1),
        ∑ i ∈ range (e + 1), ∑ α ∈ range (u + 1), F u α e i γ =
      ∑ A ∈ range (N + 1), ∑ m ∈ range (N - A + 1), ∑ i ∈ range (A + 1), ∑ q ∈ range (m + 1),
        ∑ j ∈ range (N - A - m + 1), F' A m i q j := by
  simp only [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ => ⟨x.2.2.2.2 + x.2.2.2.1, x.1 - x.2.2.2.2 + x.2.2.1, x.2.2.2.1, x.1 - x.2.2.2.2,
      x.2.1 - x.2.2.2.1⟩)
    (fun y _ => ⟨y.1 - y.2.2.1 + y.2.2.2.1, y.2.2.1 + y.2.2.2.2, y.2.1 - y.2.2.2.1, y.2.2.1,
      y.1 - y.2.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, e, γ, i, α⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    obtain ⟨_, _, _, _, _⟩ := hx
    omega
  · rintro ⟨A, m, i, q, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    obtain ⟨_, _, _, _, _⟩ := hy
    omega
  · rintro ⟨u, e, γ, i, α⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨_, _, _, _, _⟩ := hx
    dsimp only
    simp only [show α + i - i = α by omega, show α + (u - α) = u by omega,
      show i + (e - i) = e by omega, show u - α + γ - (u - α) = γ by omega]
  · rintro ⟨A, m, i, q, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    obtain ⟨_, _, _, _, _⟩ := hy
    dsimp only
    simp only [show A - i + i = A by omega, show A - i + q - (A - i) = q by omega,
      show q + (m - q) = m by omega, show i + j - i = j by omega]
  · rintro ⟨u, e, γ, i, α⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨_, _, _, _, _⟩ := hx
    exact h u α e i γ (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Reindexing `(A, m) ↦ (N - A - m, m)` of a triangular double sum. -/
theorem reindex2 (N : ℕ) (F : ℕ → ℕ → ℚ) :
    ∑ A ∈ range (N + 1), ∑ m ∈ range (N - A + 1), F A m =
      ∑ B ∈ range (N + 1), ∑ m ∈ range (N - B + 1), F (N - B - m) m := by
  simp only [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨N - x.1 - x.2, x.2⟩) (fun y _ => ⟨N - y.1 - y.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨B, m⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨A, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    simp only [show N - (N - A - m) - m = A by omega]
  · rintro ⟨B, m⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    dsimp only
    simp only [show N - (N - B - m) - m = B by omega]
  · rintro ⟨A, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    dsimp only
    rw [show N - (N - A - m) - m = A by omega]

/-- First part of `H` (generating function `β(x-z)(β(x+y)-β(y+z))/(x-z)`). -/
noncomputable def H1 (A m B : ℕ) : ℚ :=
  ∑ i ∈ range (A + 1), ∑ q ∈ range (m + 1), ∑ j ∈ range (B + 1),
    (-1 : ℚ) ^ q * ((A - i + q).choose (A - i) : ℚ) * bb (A - i + q) * ((i + j).choose i : ℚ) *
      ((m - q + (B - j)).choose (m - q) : ℚ) * bb (i + j + 1 + (m - q + (B - j)))

/-- Second part of `H`, in the symmetric form `(-1)^m H₁(B,m,A)`. -/
noncomputable def H2 (A m B : ℕ) : ℚ := (-1 : ℚ) ^ m * H1 B m A

/-- Third part of `H`. -/
noncomputable def H3 (A m B : ℕ) : ℚ := if m = 0 then ((A + B).choose A : ℚ) * bb (A + B) else 0

theorem expand_H (a b c : ℚ) (N : ℕ) :
    coeff N (rescale (a - c) (bernoulliPowerSeries ℚ) * G (a - c) (b + c)) =
      ∑ A ∈ range (N + 1), ∑ m ∈ range (N - A + 1),
        a ^ A * c ^ m * b ^ (N - A - m) * H1 A m (N - A - m) := by
  have hL : coeff N (rescale (a - c) (bernoulliPowerSeries ℚ) * G (a - c) (b + c)) =
      ∑ u ∈ range (N + 1), ∑ e ∈ range (N - u + 1), ∑ γ ∈ range (N - u - e + 1),
        ∑ i ∈ range (e + 1), ∑ α ∈ range (u + 1),
          a ^ α * (-c) ^ (u - α) * (u.choose α : ℚ) * bb u * bb (N - u + 1) *
            (a ^ i * b ^ (e - i) * (e.choose i : ℚ)) *
            (c ^ γ * b ^ (N - u - e - γ) * ((N - u - e).choose γ : ℚ)) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [coeff_resc_beta, G, coeff_mk, show a - c + (b + c) = a + b by ring,
      show b + c = c + b by ring, sub_eq_add_neg]
    simp only [add_pow, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun γ _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hL]
  simp only [H1, Finset.mul_sum]
  refine reindex5 N _ _ fun u α e i γ hu hα he hi hγ => ?_
  have e1 : α + i - i = α := by omega
  have e2 : α + (u - α) = u := by omega
  have e3 : u - α + γ - (u - α) = γ := by omega
  have e4 : N - (α + i) - (u - α + γ) - (e - i) = N - u - e - γ := by omega
  have e5 : i + (e - i) = e := by omega
  have e6 : γ + (N - u - e - γ) = N - u - e := by omega
  have e7 : e + 1 + (N - u - e) = N - u + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7, neg_pow,
    show N - (α + i) - (u - α + γ) = (e - i) + (N - u - e - γ) by omega,
    show u - α + γ = (u - α) + γ by omega, pow_add, pow_add, pow_add]
  ring

/-- Lemma 3(e), coefficient form: `H₁ + H₂ + H₃ = 0`. -/
theorem H_zero (A m B : ℕ) : H1 A m B + H2 A m B + H3 A m B = 0 := by
  have key : ∀ N, ∀ B ≤ N, ∀ z : ℕ, 2 ≤ z →
      ∑ m ∈ range (N - B + 1), (H1 (N - B - m) m B + H2 (N - B - m) m B + H3 (N - B - m) m B) *
        (z : ℚ) ^ m = 0 := by
    intro N B hB z hz
    revert B
    refine poly_vanish N _ ?_
    intro t ht
    have hz2 : (2 : ℚ) ≤ z := by exact_mod_cast hz
    have ht2 : (2 : ℚ) ≤ t := by exact_mod_cast ht
    have hP : (1 : ℚ) - z ≠ 0 := by intro h; linarith
    have hQ : (t : ℚ) + z ≠ 0 := by intro h; linarith
    have hPQ : (1 : ℚ) - z + (t + z) ≠ 0 := by intro h; linarith
    have hphi := congrArg (coeff N) (Phi_zero hP hQ hPQ)
    rw [map_add, map_add, map_zero] at hphi
    have p1 := expand_H 1 t z N
    have p2 : coeff N (rescale ((t : ℚ) + z) (bernoulliPowerSeries ℚ) * G (t + z) (1 - z)) =
        ∑ A ∈ range (N + 1), ∑ m ∈ range (N - A + 1),
          (t : ℚ) ^ A * (-(z : ℚ)) ^ m * 1 ^ (N - A - m) * H1 A m (N - A - m) := by
      have := expand_H t 1 (-z) N
      rwa [show (t : ℚ) - -z = t + z by ring, show (1 : ℚ) + -z = 1 - z by ring] at this
    have p3 : coeff N (rescale ((1 : ℚ) - z + (t + z)) (bernoulliPowerSeries ℚ)) =
        ∑ B ∈ range (N + 1), (t : ℚ) ^ B * ((N.choose B : ℚ) * bb N) := by
      rw [coeff_resc_beta, show (1 : ℚ) - z + (t + z) = t + 1 by ring, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      ring
    rw [p1, p2, p3, reindex2] at hphi
    rw [← hphi, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B hB => ?_
    simp only [Finset.mem_range] at hB
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    have h3 : ∑ m ∈ range (N - B + 1), H3 (N - B - m) m B * (z : ℚ) ^ m * (t : ℚ) ^ B =
        (t : ℚ) ^ B * ((N.choose B : ℚ) * bb N) := by
      rw [Finset.sum_eq_single 0]
      · simp only [H3, ↓reduceIte, pow_zero, mul_one, Nat.sub_zero,
          show N - B + B = N by omega]
        rw [Nat.choose_symm (by omega)]
        ring
      · intro m _ hm; simp [H3, hm]
      · simp
    rw [← h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_range] at hm
    simp only [H2, one_pow, mul_one]
    rw [neg_pow, show N - (N - B - m) - m = B by omega]
    ring
  have h := key (A + m + B) B (by omega)
  have h2 : ∀ z : ℕ, 2 ≤ z → ∑ m' ∈ range (A + m + 1),
      (H1 (A + m - m') m' B + H2 (A + m - m') m' B + H3 (A + m - m') m' B) * (z : ℚ) ^ m' = 0 := by
    intro z hz
    have := h z hz
    rw [show A + m + B - B = A + m by omega] at this
    exact this
  have := poly_vanish (A + m) _ h2 m (by omega)
  rwa [show A + m - m = A by omega] at this

end TSI
```

### `TsiCut.lean`

```lean
import TsiShuffle
import TsiBern

/-! # Lemma 1 (cut formula) for the uri multiplicities -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- Indicator as a rational number. -/
def I (p : Prop) [Decidable p] : ℚ := if p then 1 else 0

/-- The cut weight `b_{ℓP} [|Q| > d] / ℓQ!`. -/
noncomputable def phi (d : ℕ) (P Q : List ℤ) : ℚ := bb P.length * ff Q.length * I ((d : ℤ) < Q.sum)

/-- All letters are nonnegative. -/
def Nonneg (w : List ℤ) : Prop := ∀ x ∈ w, 0 ≤ x

theorem take_sum_mono {α : List ℤ} (h : Nonneg α) {j k : ℕ} (hjk : j ≤ k) :
    (α.take j).sum ≤ (α.take k).sum := by
  have e := List.sum_take_add_sum_drop (α.take k) j
  rw [List.take_take, Nat.min_eq_left hjk] at e
  have : 0 ≤ ((α.take k).drop j).sum :=
    List.sum_nonneg fun x hx => h x (List.mem_of_mem_take (List.mem_of_mem_drop hx))
  linarith

theorem take_sum_nonneg {α : List ℤ} (h : Nonneg α) (k : ℕ) : 0 ≤ (α.take k).sum :=
  List.sum_nonneg fun x hx => h x (List.mem_of_mem_take hx)

theorem B1_eq (m n : ℕ) (hn : n ≤ m) : B1 m n = ∑ k ∈ range n, bb k * ff (m - k) := by
  unfold B1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hc := choose_mul_ff k (m - k)
  rw [show k + (m - k) = m by omega] at hc
  unfold bb
  have hf : (1 / (m.factorial : ℚ)) = ff m := rfl
  rw [hf]
  have : bernoulli k / k.factorial * ff (m - k) = bernoulli k * (ff k * ff (m - k)) := by
    unfold ff; ring
  rw [this, ← hc]; ring

/-- Lemma 1: `μ_{|α|-d, α} = ∑_{α = PQ} b_{ℓP} [|Q| > d] / ℓQ!` for `α` with nonnegative letters. -/
theorem cut_formula (α : List ℤ) (hα : Nonneg α) (d : ℕ) (t : ℤ) (ht : t + d = α.sum) :
    mu t α = ss (phi d) α := by
  have hsplit : ∀ k, (α.take k).sum + (α.drop k).sum = α.sum := List.sum_take_add_sum_drop α
  unfold mu muB
  by_cases ht0 : t ≤ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht0)]
    symm
    unfold ss
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := hsplit k
    have h2 := take_sum_nonneg hα k
    unfold phi I
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ht0)]
    have hne : α ≠ [] := by rintro rfl; simp at ht; omega
    have hle : t ≤ α.sum := by omega
    have hex : ∃ j, 1 ≤ j ∧ j ≤ α.length ∧ t ≤ (α.take j).sum :=
      ⟨α.length, Nat.one_le_iff_ne_zero.mpr (by simpa using hne), le_rfl, by simpa using hle⟩
    have hind : ind t α = Nat.find hex := by
      unfold ind; rw [dite_eq_left_of_eq_true (eq_true ⟨hne, hle⟩)]
    set n := Nat.find hex with hn
    have hspec := Nat.find_spec hex
    rw [← hn] at hspec
    have hmin : ∀ k < n, ¬ (1 ≤ k ∧ k ≤ α.length ∧ t ≤ (α.take k).sum) := fun k hk =>
      Nat.find_min hex hk
    rw [hind, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), B1_eq _ _ hspec.2.1]
    unfold ss phi I
    have hiff : ∀ k ∈ range (α.length + 1), ((d : ℤ) < (α.drop k).sum ↔ k < n) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have h1 := hsplit k
      constructor
      · intro hd
        by_contra hkn
        have := take_sum_mono hα (show n ≤ k by omega)
        omega
      · intro hkn
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at h1 ⊢; omega
        · have := hmin k hkn
          have : ¬ t ≤ (α.take k).sum := fun h => this ⟨h0, by omega, h⟩
          omega
    symm
    have hterm : ∀ k ∈ range (α.length + 1),
        bb (α.take k).length * ff (α.drop k).length *
            (if (d : ℤ) < (α.drop k).sum then 1 else 0) =
          if k < n then bb k * ff (α.length - k) else 0 := by
      intro k hk
      have hk' := hiff k hk
      simp only [Finset.mem_range] at hk
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      by_cases hkn : k < n
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hk'.mpr hkn)), ite_eq_left_of_eq_true _ _ (eq_true hkn)]
        ring
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hkn (hk'.mp h)),
          ite_eq_right_of_eq_false _ _ (eq_false hkn)]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
      show (range (α.length + 1)).filter (· < n) = range n by ext k; simp; omega]

end TSI
```

### `TsiConv.lean`

```lean
import TsiCut

/-! # From the literal formal sums to shuffle sums and cut sums -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- `ν_d(w) = ∑_{w = PQ} b_{ℓP} [|Q| > d] / ℓQ!` (right side of Lemma 1). -/
noncomputable def nu (d : ℕ) (w : List ℤ) : ℚ := ss (phi d) w

/-- `P(a,b) = C(a+b,a) b_{a+b}`. -/
noncomputable def Pw (a b : ℕ) : ℚ := ((a + b).choose a : ℚ) * bb (a + b)

theorem nonneg_append {u v : List ℤ} (hu : Nonneg u) (hv : Nonneg v) : Nonneg (u ++ v) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  exacts [hu x h, hv x h]

theorem nonneg_cons {x : ℤ} {u : List ℤ} (hx : 0 ≤ x) (hu : Nonneg u) : Nonneg (x :: u) := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · rw [h]; exact hx
  · exact hu y h

theorem nonneg_of_perm {u w : List ℤ} (h : w.Perm u) (hu : Nonneg u) : Nonneg w :=
  fun x hx => hu x (h.subset hx)

theorem nonneg_take {u : List ℤ} (hu : Nonneg u) (i : ℕ) : Nonneg (u.take i) :=
  fun x hx => hu x (List.mem_of_mem_take hx)

theorem nonneg_drop {u : List ℤ} (hu : Nonneg u) (i : ℕ) : Nonneg (u.drop i) :=
  fun x hx => hu x (List.mem_of_mem_drop hx)

theorem nonneg_reverse {u : List ℤ} (hu : Nonneg u) : Nonneg u.reverse :=
  fun x hx => hu x (List.mem_reverse.mp hx)

/-! ## Formal sums -/

theorem muF_cons (B : ℕ → ℕ → ℚ) (a : ℤ) (p : ℤ × List ℤ) (A : FSum) :
    muF B a (p :: A) = (p.1 : ℚ) * muB B a p.2 + muF B a A := by
  simp [muF]

theorem muF_append (B : ℕ → ℕ → ℚ) (a : ℤ) (A C : FSum) :
    muF B a (A ++ C) = muF B a A + muF B a C := by
  simp [muF, List.map_append, List.sum_append]

theorem muF_map (B : ℕ → ℕ → ℚ) (a k : ℤ) (f : List ℤ → List ℤ) :
    ∀ L : List (List ℤ), muF B a (L.map fun w => (k, f w)) =
      (k : ℚ) * (L.map fun w => muB B a (f w)).sum
  | [] => by simp [muF]
  | w :: L => by
    rw [List.map_cons, muF_cons, muF_map B a k f L]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem muF_map_id (B : ℕ → ℕ → ℚ) (a k : ℤ) (L : List (List ℤ)) :
    muF B a (L.map fun w => (k, w)) = (k : ℚ) * (L.map (muB B a)).sum := by
  simpa using muF_map B a k (fun w => w) L

theorem muF_flatMap (B : ℕ → ℕ → ℚ) (a : ℤ) (g : List ℤ → FSum) :
    ∀ L : List (List ℤ), muF B a (L.flatMap g) = (L.map fun w => muF B a (g w)).sum
  | [] => by simp [muF]
  | w :: L => by
    rw [List.flatMap_cons, muF_append, muF_flatMap B a g L]
    simp

theorem shuffleF_single (k₁ k₂ : ℤ) (u v : List ℤ) :
    shuffleF [(k₁, u)] [(k₂, v)] = (shuffle u v).map fun w => (k₁ * k₂, w) := by
  simp [shuffleF]

theorem catF_single (A : FSum) (k : ℤ) (z : List ℤ) :
    catF A [(k, z)] = A.map fun p => (p.1 * k, p.2 ++ z) := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    simp only [catF, List.flatMap_cons, List.map_cons, List.map_nil, List.singleton_append] at ih ⊢
    rw [ih]

theorem catF_map (L M : List (List ℤ)) (k k' : ℤ) (f : List ℤ → List ℤ) :
    catF (L.map fun w => (k, f w)) (M.map fun w' => (k', w')) =
      L.flatMap fun w => M.map fun w' => (k * k', f w ++ w') := by
  simp [catF, List.flatMap_map, List.map_map, Function.comp_def]

theorem muF_idx (B : ℕ → ℕ → ℚ) (a : ℤ) (w : List ℤ) : muF B a (idx w) = muB B a w := by
  simp [muF, idx]

theorem muF_sh_idx (B : ℕ → ℕ → ℚ) (a : ℤ) (u v : List ℤ) :
    muF B a (shuffleF (idx u) (idx v)) = Sh (muB B a) u v := by
  rw [idx, idx, shuffleF_single, muF_map_id]
  simp [Sh]

theorem muF_sh_rev (B : ℕ → ℕ → ℚ) (a : ℤ) (u v : List ℤ) :
    muF B a (shuffleF (idx u) (revF v)) = (-1 : ℚ) ^ v.length * Sh (muB B a) u v.reverse := by
  rw [idx, revF, shuffleF_single, muF_map_id]
  simp [Sh]

theorem muF_cat_i (B : ℕ → ℕ → ℚ) (a c : ℤ) (u v z : List ℤ) :
    muF B a (catF (catF (shuffleF (idx u) (idx v)) (idx [c])) (idx z)) =
      Sh (fun w => muB B a (w ++ c :: z)) u v := by
  rw [idx, idx, idx, idx, shuffleF_single, catF_single, catF_single]
  simp only [List.map_map, Function.comp_def]
  rw [muF_map B a (1 * 1 * 1 * 1) (fun w => w ++ [c] ++ z)]
  simp [Sh]

theorem muF_cat_ii (B : ℕ → ℕ → ℚ) (a c : ℤ) (u v x y : List ℤ) :
    muF B a (catF (catF (shuffleF (idx u) (revF v)) (idx [c])) (shuffleF (idx x) (revF y))) =
      (-1 : ℚ) ^ v.length * (-1 : ℚ) ^ y.length *
        Sh (fun w => Sh (fun w' => muB B a (w ++ c :: w')) x y.reverse) u v.reverse := by
  rw [idx, idx, idx, revF, revF, shuffleF_single, shuffleF_single, catF_single]
  simp only [List.map_map, Function.comp_def]
  rw [catF_map (shuffle u v.reverse) (shuffle x y.reverse) _ _ (fun w => w ++ [c]),
    muF_flatMap]
  unfold Sh
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  rw [muF_map B a _ (fun w' => w ++ [c] ++ w')]
  simp

/-! ## Lemma 1 on shuffles -/

theorem mu_nonpos {a : ℤ} (h : a ≤ 0) (w : List ℤ) : mu a w = 0 := by
  simp [mu, muB, h]

theorem Sh_mu_nonpos {a : ℤ} (h : a ≤ 0) (u v : List ℤ) : Sh (mu a) u v = 0 := by
  have : mu a = fun _ => 0 := funext (mu_nonpos h)
  simp [Sh, this]

theorem mu_eq_nu {w : List ℤ} (hw : Nonneg w) {t : ℤ} {d : ℕ} (h : t + d = w.sum) :
    mu t w = nu d w := cut_formula w hw d t h

theorem Sh_mu_nu {u v : List ℤ} (hu : Nonneg u) (hv : Nonneg v) {t : ℤ} {d : ℕ}
    (h : t + d = u.sum + v.sum) : Sh (mu t) u v = Sh (nu d) u v := by
  refine Sh_congr fun w hw => ?_
  have hp := perm_of_mem_shuffle u v w hw
  exact mu_eq_nu (nonneg_of_perm hp (nonneg_append hu hv)) (by rw [hp.sum_eq, List.sum_append, h])

/-- The summand of Def. A.5(i), first kind, in cut form. -/
theorem term_i {u₁ u₂ v₁ v₂ : List ℤ} (h₁ : Nonneg u₁) (h₂ : Nonneg u₂) (h₃ : Nonneg v₁)
    (h₄ : Nonneg v₂) (d₁ d₂ : ℕ) (t : ℤ) (ht : t + d₁ + d₂ = u₁.sum + u₂.sum + v₁.sum + v₂.sum) :
    mu (u₂.sum - d₁) u₂ * Sh (fun w => mu t (w ++ (u₂.sum - d₁) :: v₂)) u₁ v₁ =
      nu d₁ u₂ * Sh (fun w => nu d₂ (w ++ (u₂.sum - d₁) :: v₂)) u₁ v₁ := by
  have e1 : mu (u₂.sum - d₁) u₂ = nu d₁ u₂ := mu_eq_nu h₂ (by ring)
  by_cases hc : u₂.sum - d₁ ≤ 0
  · rw [← e1, mu_nonpos hc, zero_mul, zero_mul]
  · rw [e1]
    congr 1
    refine Sh_congr fun w hw => ?_
    have hp := perm_of_mem_shuffle u₁ v₁ w hw
    refine mu_eq_nu ?_ ?_
    · exact nonneg_append (nonneg_of_perm hp (nonneg_append h₁ h₃)) (nonneg_cons (by omega) h₄)
    · rw [List.sum_append, List.sum_cons, hp.sum_eq, List.sum_append]; linarith

/-- The summand of Def. A.5(ii) in cut form. -/
theorem term_ii {p q u v x y : List ℤ} (hp : Nonneg p) (hq : Nonneg q) (hu : Nonneg u)
    (hv : Nonneg v) (hx : Nonneg x) (hy : Nonneg y) (d d' : ℕ) (t : ℤ)
    (ht : t + d + d' = p.sum + q.sum + u.sum + v.sum + x.sum + y.sum) :
    Sh (mu (p.sum + q.sum - d)) p q *
        Sh (fun w => Sh (fun w' => mu t (w ++ (p.sum + q.sum - d) :: w')) x y) u v =
      Sh (nu d) p q * Sh (fun w => Sh (fun w' => nu d' (w ++ (p.sum + q.sum - d) :: w')) x y) u v := by
  have e1 : Sh (mu (p.sum + q.sum - d)) p q = Sh (nu d) p q := Sh_mu_nu hp hq (by ring)
  by_cases hc : p.sum + q.sum - d ≤ 0
  · rw [← e1, Sh_mu_nonpos hc, zero_mul, zero_mul]
  · rw [e1]
    congr 1
    refine Sh_congr fun w hw => ?_
    have hpw := perm_of_mem_shuffle u v w hw
    refine Sh_congr fun w' hw' => ?_
    have hpw' := perm_of_mem_shuffle x y w' hw'
    refine mu_eq_nu ?_ ?_
    · exact nonneg_append (nonneg_of_perm hpw (nonneg_append hu hv))
        (nonneg_cons (by omega) (nonneg_of_perm hpw' (nonneg_append hx hy)))
    · rw [List.sum_append, List.sum_cons, hpw.sum_eq, hpw'.sum_eq, List.sum_append,
        List.sum_append]
      linarith

end TSI
```

### `TsiShL.lean`

```lean
import TsiConv

/-! # Shuffle sums of cut sums (Lemma 2 in closed form) and split-sum rearrangements -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem Sh_rep {f : List ℤ → ℚ}
    (hf : ∀ w w' : List ℤ, w.length = w'.length → w.sum = w'.sum → f w = f w') (u v : List ℤ) :
    Sh f u v = ((u.length + v.length).choose u.length : ℚ) * f (u ++ v) :=
  Sh_const _ fun w hw => hf w (u ++ v) hw.length_eq hw.sum_eq

/-- Lemma 2 for `ν`: `∑_{w ∈ u ⧢ v} ν_d(w)`. -/
theorem Sh_nu (d : ℕ) (u v : List ℤ) :
    Sh (nu d) u v = ss (fun u₁ u₂ => ss (fun v₁ v₂ =>
      Pw u₁.length v₁.length * (ff u₂.length * ff v₂.length * I ((d : ℤ) < u₂.sum + v₂.sum))) v) u := by
  unfold nu
  rw [Sh_ss]
  refine ss_ext _ fun u₁ u₂ => ss_ext _ fun v₁ v₂ => ?_
  rw [Sh_ext u₁ v₁ (fun P => Sh_rep (f := phi d P) (fun w w' hl hs => by simp [phi, hl, hs]) u₂ v₂)]
  rw [Sh_rep (fun w w' hl hs => by simp [phi, hl])]
  simp only [phi, List.length_append, List.sum_append, Pw]
  rw [← choose_mul_ff u₂.length v₂.length]
  ring

/-- The same with the second word reversed. -/
theorem Sh_nu_rev (d : ℕ) (u v : List ℤ) :
    Sh (nu d) u v.reverse = ss (fun u₁ u₂ => ss (fun a b =>
      Pw u₁.length b.length * (ff u₂.length * ff a.length * I ((d : ℤ) < u₂.sum + a.sum))) v) u := by
  rw [Sh_nu]
  refine ss_ext _ fun u₁ u₂ => ?_
  rw [ss_reverse]
  simp

/-- Cuts whose suffix contains a fixed tail `z`, summed over shuffles. -/
theorem Sh_B (d : ℕ) (z u v : List ℤ) :
    Sh (fun w => ss (fun P Q => phi d P (Q ++ z)) w) u v =
      ss (fun u₁ u₂ => ss (fun v₁ v₂ => Pw u₁.length v₁.length *
        (((u₂.length + v₂.length).choose u₂.length : ℚ) * ff (u₂.length + v₂.length + z.length) *
          I ((d : ℤ) < u₂.sum + v₂.sum + z.sum))) v) u := by
  rw [Sh_ss]
  refine ss_ext _ fun u₁ u₂ => ss_ext _ fun v₁ v₂ => ?_
  rw [Sh_ext u₁ v₁ (fun P => Sh_rep (f := fun Q => phi d P (Q ++ z))
    (fun w w' hl hs => by simp [phi, hl, hs]) u₂ v₂)]
  rw [Sh_rep (fun w w' hl hs => by simp [phi, hl])]
  simp only [phi, List.length_append, List.sum_append, Pw]
  ring

/-- Identity (i): the second factor split into (B)- and (A)-cuts. -/
theorem Sh_split_i (d : ℕ) (c : ℤ) (z u v : List ℤ) :
    Sh (fun w => nu d (w ++ c :: z)) u v =
      ss (fun u₁ u₂ => ss (fun v₁ v₂ => Pw u₁.length v₁.length *
        (((u₂.length + v₂.length).choose u₂.length : ℚ) * ff (u₂.length + v₂.length + (z.length + 1)) *
          I ((d : ℤ) < u₂.sum + v₂.sum + (c + z.sum)))) v) u +
      ((u.length + v.length).choose u.length : ℚ) *
        ss (fun P Q => bb (u.length + v.length + (P.length + 1)) * ff Q.length *
          I ((d : ℤ) < Q.sum)) z := by
  unfold nu
  rw [Sh_ext u v (fun w => ss_append_cons (phi d) w c z), Sh_add, Sh_B]
  congr 1
  rw [Sh_rep (f := fun w => ss (fun P Q => phi d (w ++ c :: P) Q) z)
    (fun w w' hl hs => ss_ext _ fun P Q => by simp [phi, hl])]
  congr 1
  exact ss_ext _ fun P Q => by simp [phi, Nat.add_assoc]

/-- Identity (ii): the second factor split into (B)- and (A)-cuts. -/
theorem Sh_split_ii (d : ℕ) (c : ℤ) (x y u v : List ℤ) :
    Sh (fun X => Sh (fun N => nu d (X ++ c :: N)) x y) u v =
      ((x.length + y.length).choose x.length : ℚ) *
        ss (fun u₁ u₂ => ss (fun v₁ v₂ => Pw u₁.length v₁.length *
          (((u₂.length + v₂.length).choose u₂.length : ℚ) *
            ff (u₂.length + v₂.length + (x.length + y.length + 1)) *
            I ((d : ℤ) < u₂.sum + v₂.sum + (c + (x.sum + y.sum))))) v) u +
      ((u.length + v.length).choose u.length : ℚ) *
        ss (fun t₁ t₂ => ss (fun r₁ r₂ => ((t₁.length + r₁.length).choose t₁.length : ℚ) *
          bb (u.length + v.length + (t₁.length + r₁.length + 1)) *
          (ff t₂.length * ff r₂.length * I ((d : ℤ) < t₂.sum + r₂.sum))) y) x := by
  unfold nu
  have h1 : ∀ X, Sh (fun N => ss (phi d) (X ++ c :: N)) x y =
      ((x.length + y.length).choose x.length : ℚ) *
        ss (fun P Q => phi d P (Q ++ c :: (x ++ y))) X +
      Sh (fun N => ss (fun P Q => phi d (X ++ c :: P) Q) N) x y := by
    intro X
    rw [Sh_ext x y (fun N => ss_append_cons (phi d) X c N), Sh_add]
    congr 1
    exact Sh_rep (fun w w' hl hs => ss_ext _ fun P Q => by simp [phi, hl, hs]) x y
  rw [Sh_ext u v h1, Sh_add, Sh_mul_left, Sh_B]
  congr 1
  · congr 1
    simp
  · rw [Sh_rep (f := fun X => Sh (fun N => ss (fun P Q => phi d (X ++ c :: P) Q) N) x y)
      (fun w w' hl hs => Sh_ext _ _ fun N => ss_ext _ fun P Q => by simp [phi, hl])]
    congr 1
    rw [Sh_ss]
    refine ss_ext _ fun t₁ t₂ => ss_ext _ fun r₁ r₂ => ?_
    rw [Sh_ext t₁ r₁ (fun P => Sh_rep (f := phi d ((u ++ v) ++ c :: P))
      (fun w w' hl hs => by simp [phi, hl, hs]) t₂ r₂)]
    rw [Sh_rep (fun w w' hl hs => by simp [phi, hl])]
    simp only [phi, List.length_append, List.length_cons, List.sum_append]
    rw [← choose_mul_ff t₂.length r₂.length]
    ring_nf

/-! ## Split-sum rearrangements -/

/-- Four pieces: `w = (a b)(c e)` regrouped as `w = a ((b c) e)`. -/
theorem ss4 (G : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun x y => ss (fun a b => ss (fun c e => G a b c e) y) x) w =
      ss (fun a R => ss (fun M e => ss (fun b c => G a b c e) M) R) w := by
  rw [← ss_coassoc (fun a b y => ss (fun c e => G a b c e) y)]
  exact ss_ext _ fun a z => ss_coassoc (fun b c e => G a b c e) z

theorem ss_last_nil (g : List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => if b.length = 0 then g a else 0) w = g w := by
  unfold ss
  rw [Finset.sum_eq_single w.length]
  · simp
  · intro i hi hi0
    simp only [Finset.mem_range] at hi
    simp only [List.length_drop]
    split_ifs with h
    · omega
    · rfl
  · simp

theorem ss_nil_of_len {g : List ℤ → List ℤ → ℚ} (w : List ℤ) :
    ss (fun a b => if a.length = 0 then g a b else 0) w = g [] w := by
  rw [← ss_first_nil (g [] ·) w]
  refine ss_congr fun a b hab => ?_
  split_ifs with h
  · rw [List.length_eq_zero_iff.mp h]
  · rfl

end TSI
```

### `TsiColl.lean`

```lean
import TsiShL
import TsiCoeffH

/-! # Lemma 3 as identities of split sums -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem ss_len1 (h : ℕ → ℕ → ℚ) (X : List ℤ) :
    ss (fun a b => h a.length b.length) X = ∑ i ∈ range (X.length + 1), h i (X.length - i) :=
  ss_len h X

theorem ss_len2 (h : ℕ → ℕ → ℕ → ℕ → ℚ) (X Y : List ℤ) :
    ss (fun a b => ss (fun c e => h a.length b.length c.length e.length) Y) X =
      ∑ i ∈ range (X.length + 1), ∑ j ∈ range (Y.length + 1),
        h i (X.length - i) j (Y.length - j) := by
  unfold ss
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hi hj
  simp only [List.length_take, List.length_drop, Nat.min_eq_left (show i ≤ X.length by omega),
    Nat.min_eq_left (show j ≤ Y.length by omega)]

theorem ss_len3 (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ) (X Y Z : List ℤ) :
    ss (fun a b => ss (fun c e => ss (fun f g =>
      h a.length b.length c.length e.length f.length g.length) Z) Y) X =
      ∑ i ∈ range (X.length + 1), ∑ j ∈ range (Y.length + 1), ∑ k ∈ range (Z.length + 1),
        h i (X.length - i) j (Y.length - j) k (Z.length - k) := by
  unfold ss
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hi hj hk
  simp only [List.length_take, List.length_drop, Nat.min_eq_left (show i ≤ X.length by omega),
    Nat.min_eq_left (show j ≤ Y.length by omega), Nat.min_eq_left (show k ≤ Z.length by omega)]

/-- Lemma 3(a) on a word. -/
theorem coll_a (X : List ℤ) :
    ss (fun a b => ff (a.length + 1) * bb b.length) X = if X.length = 0 then 1 else 0 := by
  rw [ss_len1 (fun i j => ff (i + 1) * bb j), ← bern_a]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Lemma 3(b) on a word. -/
theorem coll_b (r T : ℕ) (Y : List ℤ) :
    ss (fun a b => ((r + a.length).choose r : ℚ) * ((T + b.length).choose T : ℚ) *
      ff (r + T + Y.length + 1)) Y = ff (r + T + 1) * ff Y.length := by
  rw [ss_len1 (fun i j => ((r + i).choose r : ℚ) * ((T + j).choose T : ℚ) * ff (r + T + Y.length + 1)),
    bern_b]

/-- Lemma 3(c) on two words. -/
theorem coll_c (X Y : List ℤ) :
    ss (fun a b => ss (fun c e => (-1 : ℚ) ^ c.length * Pw b.length c.length *
      ff (a.length + e.length + 1)) Y) X = if X.length = 0 then ff Y.length else 0 := by
  rw [ss_len2 (fun i i' j j' => (-1 : ℚ) ^ j * Pw i' j * ff (i + j' + 1)), ← bern_c]
  unfold cc Pw
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lemma 3(d) on two words. -/
theorem coll_d (X Y : List ℤ) :
    ss (fun a b => ss (fun c e => (-1 : ℚ) ^ a.length * Pw b.length e.length *
      ff (a.length + c.length + 1)) Y) X =
      if Y.length = 0 then (-1 : ℚ) ^ X.length * ff X.length else 0 := by
  rw [ss_len2 (fun i i' j j' => (-1 : ℚ) ^ i * Pw i' j' * ff (i + j + 1)), ← bern_d]
  unfold dd Pw
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `F` (first part, `m = 0` of `H₁`) on two words. -/
theorem coll_F (A B : List ℤ) :
    ss (fun a₁ a₂ => ss (fun b₁ b₂ => bb a₂.length *
      (((a₁.length + b₁.length).choose a₁.length : ℚ) *
        bb (a₁.length + b₁.length + (b₂.length + 1)))) B) A = H1 A.length 0 B.length := by
  rw [ss_len2 (fun i i' j j' => bb i' * (((i + j).choose i : ℚ) * bb (i + j + (j' + 1))))]
  unfold H1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_range_one, pow_zero, Nat.sub_zero, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, mul_one, Nat.zero_add, Nat.choose_self]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show i + j + 1 + (B.length - j) = i + j + (B.length - j + 1) by omega]
  ring

/-- `H₁` on three words. -/
theorem coll_H1 (A M B : List ℤ) :
    ss (fun a₁ a₂ => ss (fun m₁ m₂ => ss (fun b₁ b₂ => (-1 : ℚ) ^ m₁.length *
      Pw a₂.length m₁.length * (((a₁.length + b₁.length).choose a₁.length : ℚ) *
        ((m₂.length + b₂.length).choose m₂.length : ℚ) *
        bb (a₁.length + b₁.length + (m₂.length + b₂.length + 1)))) B) M) A =
      H1 A.length M.length B.length := by
  rw [ss_len3 (fun i i' q q' j j' => (-1 : ℚ) ^ q * Pw i' q * (((i + j).choose i : ℚ) *
    ((q' + j').choose q' : ℚ) * bb (i + j + (q' + j' + 1))))]
  unfold H1 Pw
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro j _
  rw [show i + j + 1 + (M.length - q + (B.length - j)) =
    i + j + (M.length - q + (B.length - j) + 1) by omega]
  ring

/-- `H₂` on three words. -/
theorem coll_H2 (A M B : List ℤ) :
    ss (fun a₁ a₂ => ss (fun m₁ m₂ => ss (fun b₁ b₂ => (-1 : ℚ) ^ m₁.length *
      Pw m₂.length b₂.length * (((a₁.length + b₁.length).choose a₁.length : ℚ) *
        ((a₂.length + m₁.length).choose a₂.length : ℚ) *
        bb (a₁.length + b₁.length + (a₂.length + m₁.length + 1)))) B) M) A =
      H2 A.length M.length B.length := by
  rw [ss_len3 (fun i i' q q' j j' => (-1 : ℚ) ^ q * Pw q' j' * (((i + j).choose i : ℚ) *
    ((i' + q).choose i' : ℚ) * bb (i + j + (i' + q + 1))))]
  unfold H2 H1 Pw
  simp only [Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun q hq => ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi hq hj
  rw [show M.length + 1 - 1 - q = M.length - q by omega,
    show M.length - (M.length - q) = q by omega, Nat.add_comm j i]
  rw [Nat.add_comm q (B.length - j), ← Nat.choose_symm_add (a := i) (b := j),
    Nat.choose_symm_add (a := B.length - j) (b := q),
    Nat.choose_symm_add (a := M.length - q) (b := A.length - i),
    Nat.add_comm (A.length - i) (M.length - q),
    show i + j + 1 + (M.length - q + (A.length - i)) = i + j + (M.length - q + (A.length - i) + 1)
      by omega]
  have hs : (-1 : ℚ) ^ M.length * (-1) ^ q = (-1) ^ (M.length - q) := by
    rw [← pow_add, show M.length + q = (M.length - q) + 2 * q by omega, pow_add, pow_mul]
    norm_num
  rw [← hs]
  ring

/-- `∑_{τ = (τ₁,τ₂)} (-1)^{ℓτ₁}/(ℓτ₁! ℓτ₂!) = 0` for `τ ≠ ∅`. -/
theorem coll_alt (X : List ℤ) (hX : X ≠ []) :
    ss (fun a b => (-1 : ℚ) ^ a.length * ff a.length * ff b.length) X = 0 := by
  rw [ss_len1 (fun i j => (-1 : ℚ) ^ i * ff i * ff j)]
  exact alt_ff X.length (Nat.one_le_iff_ne_zero.mpr (by simpa using hX))

end TSI
```

### `TsiRed.lean`

```lean
import TsiColl

/-! # Generic reductions of nested split sums (used for both identities) -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem I_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : I p = I q := by
  unfold I
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.mp h1) h2
  · exact absurd (h.mpr h2) h1
  · rfl

/-- `[X+Y>D](1-[X>d₁]-[Y>d₂]) = -[X>d₁][Y>d₂]`. -/
theorem bracket (d₁ d₂ : ℕ) (X Y : ℤ) :
    I (((d₁ + d₂ : ℕ) : ℤ) < X + Y) =
      I ((d₁ : ℤ) < X) * I (((d₁ + d₂ : ℕ) : ℤ) < X + Y) +
        I ((d₂ : ℤ) < Y) * I (((d₁ + d₂ : ℕ) : ℤ) < X + Y) - I ((d₁ : ℤ) < X) * I ((d₂ : ℤ) < Y) := by
  unfold I
  push_cast
  split_ifs <;> (try norm_num) <;> omega

theorem sum3_rev {ι κ μ : Type*} (s : Finset ι) (t : Finset κ) (u : Finset μ)
    (f : ι → κ → μ → ℚ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k = ∑ k ∈ u, ∑ j ∈ t, ∑ i ∈ s, f i j k := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Collapse of a split `w = (a, b)` followed by a split of `a`, via Lemma 3(b). -/
theorem thetaB (K : List ℤ → List ℤ → List ℤ → ℚ) (g : List ℤ → ℚ) (h : ℤ → ℚ) (r T : ℕ)
    (hK : ∀ y₁ y₂ z, K y₁ y₂ z = g y₁ * (((r + y₂.length).choose r : ℚ) *
      ((T + z.length).choose T : ℚ) * ff (r + T + (y₂.length + z.length) + 1)) * h (y₂.sum + z.sum))
    (w : List ℤ) :
    ss (fun w₁ w₂ => ss (fun y₁ y₂ => K y₁ y₂ w₂) w₁) w =
      ss (fun a b => g a * (ff (r + T + 1) * ff b.length) * h b.sum) w := by
  rw [← ss_coassoc (fun a c d => K a c d)]
  refine ss_ext _ fun a b => ?_
  have e : ss (fun c d => K a c d) b = ss (fun c d => g a * h b.sum *
      (((r + c.length).choose r : ℚ) * ((T + d.length).choose T : ℚ) *
        ff (r + T + b.length + 1))) b :=
    ss_congr fun c d hcd => by
      rw [hK, ← hcd]
      simp only [List.length_append, List.sum_append]
      ring
  refine e.trans ?_
  rw [← ss_mul_left, coll_b]
  ring

/-- Collapse of `w = (a b)(c e)` with weight `1/(ℓb+1)! · b_{ℓc}`, via Lemma 3(a). -/
theorem sigmaB (K : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ)
    (L : List ℤ → ℤ → ℚ) (d : ℕ)
    (hK : ∀ σ₁ σ₂ x₁ x₂ U V, x₁ ++ x₂ = σ₁ → U ++ V = σ₂ →
      K σ₁ σ₂ x₁ x₂ U V = ff (x₂.length + 1) * bb U.length * (ff V.length * I ((d : ℤ) < V.sum)) *
        L x₁ (x₂.sum + U.sum + V.sum)) (w : List ℤ) :
    ss (fun σ₁ σ₂ => ss (fun x₁ x₂ => ss (fun U V => K σ₁ σ₂ x₁ x₂ U V) σ₂) σ₁) w =
      ss (fun a b => ff b.length * I ((d : ℤ) < b.sum) * L a b.sum) w := by
  have e1 : ss (fun σ₁ σ₂ => ss (fun x₁ x₂ => ss (fun U V => K σ₁ σ₂ x₁ x₂ U V) σ₂) σ₁) w =
      ss (fun σ₁ σ₂ => ss (fun x₁ x₂ => ss (fun U V => ff (x₂.length + 1) * bb U.length *
        (ff V.length * I ((d : ℤ) < V.sum)) * L x₁ (x₂.sum + U.sum + V.sum)) σ₂) σ₁) w :=
    ss_ext _ fun σ₁ σ₂ => ss_congr fun x₁ x₂ h₁ => ss_congr fun U V h₂ => hK _ _ _ _ _ _ h₁ h₂
  rw [e1, ss4]
  refine ss_ext _ fun a R => ?_
  have e2 : ∀ M e : List ℤ, ss (fun b c => ff (b.length + 1) * bb c.length *
      (ff e.length * I ((d : ℤ) < e.sum)) * L a (b.sum + c.sum + e.sum)) M =
      if M.length = 0 then ff e.length * I ((d : ℤ) < e.sum) * L a (M.sum + e.sum) else 0 := by
    intro M e
    have e3 : ss (fun b c => ff (b.length + 1) * bb c.length *
        (ff e.length * I ((d : ℤ) < e.sum)) * L a (b.sum + c.sum + e.sum)) M =
        ss (fun b c => ff (b.length + 1) * bb c.length *
          (ff e.length * I ((d : ℤ) < e.sum) * L a (M.sum + e.sum))) M :=
      ss_congr fun b c hbc => by rw [← hbc, List.sum_append]; ring
    rw [e3, ← ss_mul_right, coll_a]
    split_ifs <;> ring
  refine (ss_ext R e2).trans ?_
  rw [ss_nil_of_len]
  simp

/-- Rearrangement used for the (B)-part of identity (i). -/
theorem rearr_iB (N : List ℤ → List ℤ → List ℤ → ℚ)
    (Bf : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (σ ϑ : List ℤ) :
    ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ => ss (N σ₂) σ₂ * ss (fun u₁ u₂ => Bf σ₁ σ₂ u₁ u₂ ϑ₁ ϑ₂) σ₁) ϑ) σ =
      ss (fun σ₁ σ₂ => ss (fun u₁ u₂ => ss (fun U V => N σ₂ U V *
        ss (fun ϑ₁ ϑ₂ => Bf σ₁ σ₂ u₁ u₂ ϑ₁ ϑ₂) ϑ) σ₂) σ₁) σ := by
  refine ss_ext _ fun σ₁ σ₂ => ?_
  unfold ss
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact sum3_rev _ _ _ _

/-- Rearrangement used for the (A)-part of identity (i). -/
theorem rearr_iA (N : List ℤ → List ℤ → ℚ) (c : List ℤ → List ℤ → ℚ)
    (M : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (σ ϑ : List ℤ) :
    ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ => ss N σ₂ * (c σ₁ ϑ₁ * ss (M σ₁ ϑ₁) ϑ₂)) ϑ) σ =
      ss (fun x V => ss (fun y Q => ss (fun σ₁ U => ss (fun ϑ₁ P =>
        N U V * (c σ₁ ϑ₁ * M σ₁ ϑ₁ P Q)) y) x) ϑ) σ := by
  have e1 : ∀ σ₁ σ₂, ss (fun ϑ₁ ϑ₂ => ss N σ₂ * (c σ₁ ϑ₁ * ss (M σ₁ ϑ₁) ϑ₂)) ϑ =
      ss (fun U V => ss (fun ϑ₁ ϑ₂ => ss (fun P Q => N U V * (c σ₁ ϑ₁ * M σ₁ ϑ₁ P Q)) ϑ₂) ϑ) σ₂ := by
    intro σ₁ σ₂
    unfold ss
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [ss_ext σ e1, ss_coassoc]
  refine ss_ext _ fun x V => ?_
  rw [ss_ext x fun σ₁ U => ss_coassoc (fun ϑ₁ P Q => N U V * (c σ₁ ϑ₁ * M σ₁ ϑ₁ P Q)) ϑ]
  exact ss_comm _ _ _

end TSI
```

### `TsiI1.lean`

```lean
import TsiRed

/-! # Identity (i): the terms of the first kind in closed form -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- `T₁ = ∑_{σ=(σ₁,σ₂), ϑ=(ϑ₁,ϑ₂)} ν_{d₁}(σ₂) ∑_{w ∈ σ₁ ⧢ ϑ₁} ν_{d₂}(w, |σ₂|-d₁, ϑ₂)`. -/
noncomputable def T1 (σ ϑ : List ℤ) (d₁ d₂ : ℕ) : ℚ :=
  ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ =>
    nu d₁ σ₂ * Sh (fun w => nu d₂ (w ++ (σ₂.sum - d₁) :: ϑ₂)) σ₁ ϑ₁) ϑ) σ

theorem T1B_eq (σ ϑ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ => nu d₁ σ₂ * ss (fun u₁ u₂ => ss (fun v₁ v₂ =>
      Pw u₁.length v₁.length * (((u₂.length + v₂.length).choose u₂.length : ℚ) *
        ff (u₂.length + v₂.length + (ϑ₂.length + 1)) *
        I ((d₂ : ℤ) < u₂.sum + v₂.sum + ((σ₂.sum - d₁) + ϑ₂.sum)))) ϑ₁) σ₁) ϑ) σ =
    ss (fun σa σb => ss (fun ϑa ϑb => ff σb.length * I ((d₁ : ℤ) < σb.sum) *
      (ff ϑb.length * (Pw σa.length ϑa.length *
        I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + ϑb.sum)))) ϑ) σ := by
  have hθ : ∀ σ₂ u₁ u₂ : List ℤ, ss (fun ϑ₁ ϑ₂ => ss (fun v₁ v₂ =>
      Pw u₁.length v₁.length * (((u₂.length + v₂.length).choose u₂.length : ℚ) *
        ff (u₂.length + v₂.length + (ϑ₂.length + 1)) *
        I ((d₂ : ℤ) < u₂.sum + v₂.sum + ((σ₂.sum - d₁) + ϑ₂.sum)))) ϑ₁) ϑ =
      ss (fun a b => Pw u₁.length a.length * (ff (u₂.length + 0 + 1) * ff b.length) *
        I (((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + b.sum)) ϑ := by
    intro σ₂ u₁ u₂
    refine thetaB _ (fun y => Pw u₁.length y.length)
      (fun s => I (((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + s)) u₂.length 0 (fun y₁ y₂ z => ?_) ϑ
    rw [I_iff (show (d₂ : ℤ) < u₂.sum + y₂.sum + ((σ₂.sum - d₁) + z.sum) ↔
      ((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + (y₂.sum + z.sum) by push_cast; omega)]
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.add_zero]
    rw [show u₂.length + y₂.length + (z.length + 1) = u₂.length + (y₂.length + z.length) + 1 by omega]
    ring
  unfold nu
  rw [rearr_iB]
  simp only [hθ]
  rw [sigmaB (L := fun x s => ss (fun a b => Pw x.length a.length * ff b.length *
    I (((d₁ + d₂ : ℕ) : ℤ) < s + b.sum)) ϑ) (d := d₁)]
  · refine ss_ext _ fun σa σb => ?_
    rw [ss_mul_left]
    refine ss_ext _ fun a b => ?_
    ring
  · intro σ₁ σ₂ x₁ x₂ U V _ h₂
    subst h₂
    unfold phi
    rw [ss_mul_left, ss_mul_left]
    refine ss_ext _ fun a b => ?_
    simp only [List.sum_append, add_assoc, add_zero]
    ring

theorem T1A_eq (σ ϑ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ => nu d₁ σ₂ *
      (((σ₁.length + ϑ₁.length).choose σ₁.length : ℚ) *
        ss (fun P Q => bb (σ₁.length + ϑ₁.length + (P.length + 1)) * ff Q.length *
          I ((d₂ : ℤ) < Q.sum)) ϑ₂)) ϑ) σ =
    ss (fun σa σb => ss (fun ϑa ϑb => ff σb.length * I ((d₁ : ℤ) < σb.sum) *
      (ff ϑb.length * (I ((d₂ : ℤ) < ϑb.sum) * H1 σa.length 0 ϑa.length))) ϑ) σ := by
  unfold nu
  rw [rearr_iA (phi d₁) (fun σ₁ ϑ₁ => ((σ₁.length + ϑ₁.length).choose σ₁.length : ℚ))
    (fun σ₁ ϑ₁ P Q => bb (σ₁.length + ϑ₁.length + (P.length + 1)) * ff Q.length *
      I ((d₂ : ℤ) < Q.sum))]
  refine ss_ext _ fun x V => ss_ext _ fun y Q => ?_
  rw [← coll_F x y]
  simp only [ss_mul_left]
  refine ss_ext _ fun σ₁ U => ss_ext _ fun ϑ₁ P => ?_
  unfold phi
  ring

theorem T1_eq (σ ϑ : List ℤ) (d₁ d₂ : ℕ) :
    T1 σ ϑ d₁ d₂ = ss (fun σa σb => ss (fun ϑa ϑb => ff σb.length * I ((d₁ : ℤ) < σb.sum) *
      (ff ϑb.length * (Pw σa.length ϑa.length * I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + ϑb.sum) +
        I ((d₂ : ℤ) < ϑb.sum) * H1 σa.length 0 ϑa.length))) ϑ) σ := by
  unfold T1
  simp only [Sh_split_i, mul_add, ss_add]
  rw [T1B_eq, T1A_eq, ← ss_add]

end TSI
```

### `TsiMainI.lean`

```lean
import TsiI1

/-! # Definition A.5(i) for the uri multiplicities -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem isComp_nonneg {w : List ℤ} (h : IsComp w) : Nonneg w := fun x hx => le_of_lt (h x hx)

theorem muB_B1 : muB B1 = mu := rfl

theorem Pw_symm (a b : ℕ) : Pw b a = Pw a b := by
  unfold Pw
  rw [Nat.add_comm b a, Nat.choose_symm_add]

/-- `F(A,B) = 0`. -/
theorem F_zero (a b : ℕ) : H1 a 0 b + H1 b 0 a + Pw a b = 0 := by
  have h := H_zero a 0 b
  simp only [H2, H3, pow_zero, one_mul, ↓reduceIte] at h
  unfold Pw
  exact h

theorem final_i_pointwise (a b : ℕ) (F G : ℚ) (X Y : ℤ) (d₁ d₂ : ℕ) :
    Pw a b * (F * G * I (((d₁ + d₂ : ℕ) : ℤ) < X + Y)) =
      F * I ((d₁ : ℤ) < X) * (G * (Pw a b * I (((d₁ + d₂ : ℕ) : ℤ) < X + Y) +
        I ((d₂ : ℤ) < Y) * H1 a 0 b)) +
      G * I ((d₂ : ℤ) < Y) * (F * (Pw b a * I (((d₂ + d₁ : ℕ) : ℤ) < Y + X) +
        I ((d₁ : ℤ) < X) * H1 b 0 a)) := by
  rw [Pw_symm a b, I_iff (show ((d₂ + d₁ : ℕ) : ℤ) < Y + X ↔ ((d₁ + d₂ : ℕ) : ℤ) < X + Y by
    push_cast; omega)]
  have Hz := F_zero a b
  have Br := bracket d₁ d₂ X Y
  linear_combination (F * G * Pw a b) * Br - (F * G * I ((d₁ : ℤ) < X) * I ((d₂ : ℤ) < Y)) * Hz

/-- **Definition A.5(i) holds for the uri multiplicities** (Conjecture A.7, part (i)). -/
theorem tsi_i (σ ϑ : List ℤ) (hσ : IsComp σ) (hϑ : IsComp ϑ) (d₁ d₂ : ℕ) :
    TSI_i B1 σ ϑ d₁ d₂ := by
  have hσ' := isComp_nonneg hσ
  have hϑ' := isComp_nonneg hϑ
  unfold TSI_i
  simp only [muF_idx, muF_sh_idx, muF_cat_i]
  rw [muB_B1]
  have hL : Sh (mu (σ.sum + ϑ.sum - d₁ - d₂)) σ ϑ = Sh (nu (d₁ + d₂)) σ ϑ :=
    Sh_mu_nu hσ' hϑ' (by push_cast; ring)
  have key : ∀ i ∈ range (σ.length + 1), ∀ j ∈ range (ϑ.length + 1),
      mu ((σ.drop i).sum - d₁) (σ.drop i) *
          Sh (fun w => mu (σ.sum + ϑ.sum - d₁ - d₂) (w ++ ((σ.drop i).sum - d₁) :: ϑ.drop j))
            (σ.take i) (ϑ.take j) +
        mu ((ϑ.drop j).sum - d₂) (ϑ.drop j) *
          Sh (fun w => mu (σ.sum + ϑ.sum - d₁ - d₂) (w ++ ((ϑ.drop j).sum - d₂) :: σ.drop i))
            (σ.take i) (ϑ.take j) =
      nu d₁ (σ.drop i) *
          Sh (fun w => nu d₂ (w ++ ((σ.drop i).sum - d₁) :: ϑ.drop j)) (σ.take i) (ϑ.take j) +
        nu d₂ (ϑ.drop j) *
          Sh (fun w => nu d₁ (w ++ ((ϑ.drop j).sum - d₂) :: σ.drop i)) (ϑ.take j) (σ.take i) := by
    intro i _ j _
    have es := List.sum_take_add_sum_drop σ i
    have et := List.sum_take_add_sum_drop ϑ j
    rw [term_i (nonneg_take hσ' i) (nonneg_drop hσ' i) (nonneg_take hϑ' j) (nonneg_drop hϑ' j)
      d₁ d₂ _ (by rw [← es, ← et]; ring)]
    rw [Sh_comm (fun w => mu (σ.sum + ϑ.sum - d₁ - d₂) (w ++ ((ϑ.drop j).sum - d₂) :: σ.drop i))
      (σ.take i) (ϑ.take j)]
    rw [term_i (nonneg_take hϑ' j) (nonneg_drop hϑ' j) (nonneg_take hσ' i) (nonneg_drop hσ' i)
      d₂ d₁ _ (by rw [← es, ← et]; ring)]
  rw [hL, Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => key i hi j hj]
  change _ = ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ =>
    nu d₁ σ₂ * Sh (fun w => nu d₂ (w ++ (σ₂.sum - d₁) :: ϑ₂)) σ₁ ϑ₁ +
      nu d₂ ϑ₂ * Sh (fun w => nu d₁ (w ++ (ϑ₂.sum - d₂) :: σ₂)) ϑ₁ σ₁) ϑ) σ
  simp only [ss_add]
  have h2 : ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ =>
      nu d₂ ϑ₂ * Sh (fun w => nu d₁ (w ++ (ϑ₂.sum - d₂) :: σ₂)) ϑ₁ σ₁) ϑ) σ = T1 ϑ σ d₂ d₁ := by
    unfold T1
    exact ss_comm _ _ _
  have h3 : T1 ϑ σ d₂ d₁ = ss (fun σa σb => ss (fun ϑa ϑb =>
      ff ϑb.length * I ((d₂ : ℤ) < ϑb.sum) *
        (ff σb.length * (Pw ϑa.length σa.length * I (((d₂ + d₁ : ℕ) : ℤ) < ϑb.sum + σb.sum) +
          I ((d₁ : ℤ) < σb.sum) * H1 ϑa.length 0 σa.length))) ϑ) σ := by
    rw [T1_eq]
    exact ss_comm _ _ _
  rw [show ss (fun σ₁ σ₂ => ss (fun ϑ₁ ϑ₂ =>
      nu d₁ σ₂ * Sh (fun w => nu d₂ (w ++ (σ₂.sum - d₁) :: ϑ₂)) σ₁ ϑ₁) ϑ) σ = T1 σ ϑ d₁ d₂ from rfl,
    h2, h3, T1_eq, Sh_nu, ← ss_add]
  refine ss_ext _ fun σa σb => ?_
  rw [← ss_add]
  refine ss_ext _ fun ϑa ϑb => ?_
  exact final_i_pointwise _ _ _ _ _ _ _ _

end TSI
```

### `TsiRedII.lean`

```lean
import TsiRed

/-! # Generic reductions of nested split sums for identity (ii) -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem ss_ite_zero (p : Prop) [Decidable p] (H : List ℤ → List ℤ → ℚ) (w : List ℤ) :
    ss (fun a b => if p then H a b else 0) w = if p then ss H w else 0 := by
  split_ifs
  · rfl
  · exact ss_zero w

/-- Factor a constant out of a double split sum. -/
theorem ss2_mul_right (P : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (c : ℚ) (X Y : List ℤ) :
    ss (fun a b => ss (fun e f => P a b e f * c) Y) X = ss (fun a b => ss (P a b) Y) X * c := by
  rw [ss_mul_right]
  exact ss_ext _ fun a b => (ss_mul_right _ _ _).symm

/-- `(∑∑ F)(∑∑ G) = ∑∑∑∑ F G`. -/
theorem prod_ss2 (F : List ℤ → List ℤ → List ℤ → List ℤ → ℚ)
    (G : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (x y z w : List ℤ) :
    ss (fun s₁ s₂ => ss (F s₁ s₂) y) x * ss (fun t₁ t₂ => ss (G t₁ t₂) w) z =
      ss (fun s₁ s₂ => ss (fun a b => ss (fun t₁ t₂ => ss (fun r₁ r₂ =>
        F s₁ s₂ a b * G t₁ t₂ r₁ r₂) w) z) y) x := by
  unfold ss
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]

/-- Collapse for the (B)-part of term 1 of (ii), via Lemma 3(c). -/
theorem sigTau (K : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ →
      List ℤ → List ℤ → ℚ) (L : List ℤ → ℤ → ℚ) (d : ℕ) (σ τ : List ℤ)
    (hK : ∀ σ₁ σ₂ τ₁ τ₂ x₁ x₂ s₁ s₂ a b, τ₁ ++ τ₂ = τ → x₁ ++ x₂ = σ₁ → s₁ ++ s₂ = σ₂ →
      a ++ b = τ₁ → K σ₁ σ₂ τ₁ τ₂ x₁ x₂ s₁ s₂ a b =
        (-1 : ℚ) ^ a.length * ((-1 : ℚ) ^ b.length * Pw s₁.length b.length *
          ff (x₂.length + τ₂.length + 1)) *
          (ff s₂.length * ff a.length * I ((d : ℤ) < s₂.sum + a.sum)) *
          L x₁ (x₂.sum + s₁.sum + s₂.sum)) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun x₁ x₂ => ss (fun s₁ s₂ => ss (fun a b =>
      K σ₁ σ₂ τ₁ τ₂ x₁ x₂ s₁ s₂ a b) τ₁) σ₂) σ₁) τ) σ =
    ss (fun σa σb => ss (fun τp τs => (-1 : ℚ) ^ τp.length * ff τs.length *
      (ff σb.length * ff τp.length * I ((d : ℤ) < σb.sum + τp.sum)) * L σa σb.sum) τ) σ := by
  -- the body in explicit form
  set G : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ :=
    fun x₁ x₂ s₁ s₂ a b τ₂ => (-1 : ℚ) ^ a.length * ((-1 : ℚ) ^ b.length * Pw s₁.length b.length *
      ff (x₂.length + τ₂.length + 1)) *
      (ff s₂.length * ff a.length * I ((d : ℤ) < s₂.sum + a.sum)) *
      L x₁ (x₂.sum + s₁.sum + s₂.sum) with hG
  have e1 : ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun x₁ x₂ => ss (fun s₁ s₂ => ss (fun a b =>
      K σ₁ σ₂ τ₁ τ₂ x₁ x₂ s₁ s₂ a b) τ₁) σ₂) σ₁) τ) σ =
      ss (fun σ₁ σ₂ => ss (fun x₁ x₂ => ss (fun s₁ s₂ => ss (fun τ₁ τ₂ => ss (fun a b =>
        G x₁ x₂ s₁ s₂ a b τ₂) τ₁) τ) σ₂) σ₁) σ := by
    refine ss_ext _ fun σ₁ σ₂ => ?_
    refine Eq.trans (ss_congr fun τ₁ τ₂ hτ => ss_congr fun x₁ x₂ hx => ss_congr fun s₁ s₂ hs =>
      ss_congr fun a b hab => hK _ _ _ _ _ _ _ _ _ _ hτ hx hs hab) ?_
    refine (ss_comm _ τ σ₁).trans (ss_ext _ fun x₁ x₂ => ?_)
    exact ss_comm _ τ σ₂
  rw [e1, ss4]
  refine ss_ext _ fun σa R => ?_
  -- inside: ∑_{R = (M, s₂)} ∑_{M = (x₂, s₁)} ∑_{τ = (τ₁,τ₂)} ∑_{τ₁ = (a,b)} G
  have e2 : ∀ M s₂ : List ℤ, ss (fun x₂ s₁ => ss (fun τ₁ τ₂ => ss (fun a b =>
      G σa x₂ s₁ s₂ a b τ₂) τ₁) τ) M =
      if M.length = 0 then ss (fun τp τs => (-1 : ℚ) ^ τp.length * ff τs.length *
        (ff s₂.length * ff τp.length * I ((d : ℤ) < s₂.sum + τp.sum)) * L σa (M.sum + s₂.sum)) τ
      else 0 := by
    intro M s₂
    rw [ss_ext M fun x₂ s₁ => (ss_coassoc (fun a b τ₂ => G σa x₂ s₁ s₂ a b τ₂) τ).symm]
    rw [ss_comm, ← ss_ite_zero]
    refine ss_ext _ fun τp τs => ?_
    have e3 : ss (fun x₂ s₁ => ss (fun b τ₂ => G σa x₂ s₁ s₂ τp b τ₂) τs) M =
        ss (fun x₂ s₁ => ss (fun b τ₂ => (-1 : ℚ) ^ b.length * Pw s₁.length b.length *
          ff (x₂.length + τ₂.length + 1) * ((-1 : ℚ) ^ τp.length *
            (ff s₂.length * ff τp.length * I ((d : ℤ) < s₂.sum + τp.sum)) *
            L σa (M.sum + s₂.sum))) τs) M :=
      ss_congr fun x₂ s₁ hM => ss_ext _ fun b τ₂ => by
        rw [hG, ← hM, List.sum_append]
        ring
    rw [e3, ss2_mul_right, coll_c]
    split_ifs <;> ring
  refine (ss_ext R e2).trans ?_
  rw [ss_nil_of_len]
  simp

end TSI
```

### `TsiRedII2.lean`

```lean
import TsiRedII

/-! # The collapse for the (B)-part of term 2 of identity (ii) (Lemma 3(d)) -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem rhoTau (K : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ →
      List ℤ → List ℤ → ℚ) (L : List ℤ → ℤ → ℚ) (d : ℕ) (τ ρ : List ℤ)
    (hK : ∀ τ₁ τ₂ ρ₁ ρ₂ t₁ t₂ y₁ y₂ r₁ r₂, τ₁ ++ τ₂ = τ → t₁ ++ t₂ = τ₂ → y₁ ++ y₂ = ρ₁ →
      r₁ ++ r₂ = ρ₂ → K τ₁ τ₂ ρ₁ ρ₂ t₁ t₂ y₁ y₂ r₁ r₂ =
        (-1 : ℚ) ^ τ₁.length * Pw t₁.length r₁.length * ff (y₂.length + τ₁.length + 1) *
          (ff t₂.length * ff r₂.length * I ((d : ℤ) < t₂.sum + r₂.sum)) *
          L y₁ (y₂.sum + r₁.sum + r₂.sum)) :
    ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => ss (fun t₁ t₂ => ss (fun y₁ y₂ => ss (fun r₁ r₂ =>
      K τ₁ τ₂ ρ₁ ρ₂ t₁ t₂ y₁ y₂ r₁ r₂) ρ₂) ρ₁) τ₂) ρ) τ =
    ss (fun τp τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length * ff τp.length *
      (ff τs.length * ff ρb.length * I ((d : ℤ) < τs.sum + ρb.sum)) * L ρa ρb.sum) ρ) τ := by
  set G : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ :=
    fun τ₁ t₁ t₂ y₁ y₂ r₁ r₂ => (-1 : ℚ) ^ τ₁.length * Pw t₁.length r₁.length *
      ff (y₂.length + τ₁.length + 1) *
      (ff t₂.length * ff r₂.length * I ((d : ℤ) < t₂.sum + r₂.sum)) *
      L y₁ (y₂.sum + r₁.sum + r₂.sum) with hG
  have e1 : ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => ss (fun t₁ t₂ => ss (fun y₁ y₂ => ss (fun r₁ r₂ =>
      K τ₁ τ₂ ρ₁ ρ₂ t₁ t₂ y₁ y₂ r₁ r₂) ρ₂) ρ₁) τ₂) ρ) τ =
      ss (fun τ₁ τ₂ => ss (fun t₁ t₂ => ss (fun ρ₁ ρ₂ => ss (fun y₁ y₂ => ss (fun r₁ r₂ =>
        G τ₁ t₁ t₂ y₁ y₂ r₁ r₂) ρ₂) ρ₁) ρ) τ₂) τ := by
    refine ss_congr fun τ₁ τ₂ hτ => ?_
    refine Eq.trans (ss_ext _ fun ρ₁ ρ₂ => ss_congr fun t₁ t₂ ht => ss_congr fun y₁ y₂ hy =>
      ss_congr fun r₁ r₂ hr => hK _ _ _ _ _ _ _ _ _ _ hτ ht hy hr) ?_
    exact ss_comm _ ρ τ₂
  rw [e1, ss_coassoc]
  refine ss_ext _ fun τp τs => ?_
  rw [ss_ext τp fun τ₁ t₁ => ss4 (fun y₁ y₂ r₁ r₂ => G τ₁ t₁ τs y₁ y₂ r₁ r₂) ρ]
  rw [ss_comm]
  refine ss_ext _ fun ρa R => ?_
  rw [ss_comm]
  have e2 : ∀ M r₂ : List ℤ, ss (fun τ₁ t₁ => ss (fun y₂ r₁ => G τ₁ t₁ τs ρa y₂ r₁ r₂) M) τp =
      if M.length = 0 then (-1 : ℚ) ^ τp.length * ff τp.length *
        (ff τs.length * ff r₂.length * I ((d : ℤ) < τs.sum + r₂.sum)) * L ρa (M.sum + r₂.sum)
      else 0 := by
    intro M r₂
    have e3 : ss (fun τ₁ t₁ => ss (fun y₂ r₁ => G τ₁ t₁ τs ρa y₂ r₁ r₂) M) τp =
        ss (fun τ₁ t₁ => ss (fun y₂ r₁ => (-1 : ℚ) ^ τ₁.length * Pw t₁.length r₁.length *
          ff (τ₁.length + y₂.length + 1) *
          ((ff τs.length * ff r₂.length * I ((d : ℤ) < τs.sum + r₂.sum)) *
            L ρa (M.sum + r₂.sum))) M) τp :=
      ss_ext _ fun τ₁ t₁ => ss_congr fun y₂ r₁ hM => by
        rw [hG, ← hM, List.sum_append, Nat.add_comm τ₁.length y₂.length]
        ring
    rw [e3, ss2_mul_right, coll_d]
    split_ifs <;> ring
  refine (ss_ext R e2).trans ?_
  rw [ss_nil_of_len]
  simp

end TSI
```

### `TsiII1.lean`

```lean
import TsiRedII2

/-! # Identity (ii): the (B)-part of the terms of the first kind -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem rearr_A1 (c S : ℚ) (k : List ℤ → ℚ)
    (B : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (σ₁ ρ : List ℤ) :
    ss (fun ρ₁ ρ₂ => c * (S * (k ρ₂ * ss (fun u₁ u₂ => ss (fun v₁ v₂ => B u₁ u₂ ρ₂ v₁ v₂) ρ₁) σ₁))) ρ =
      c * S * ss (fun u₁ u₂ => ss (fun ρ₁ ρ₂ => ss (fun v₁ v₂ => k ρ₂ * B u₁ u₂ ρ₂ v₁ v₂) ρ₁) ρ) σ₁ := by
  unfold ss
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem rearr_C (c : ℚ) (F : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (X : List ℤ → List ℤ → ℚ)
    (σ₂ τ₁ σ₁ : List ℤ) :
    c * ss (fun s₁ s₂ => ss (F s₁ s₂) τ₁) σ₂ * ss X σ₁ =
      ss (fun u₁ u₂ => ss (fun s₁ s₂ => ss (fun a b => c * F s₁ s₂ a b * X u₁ u₂) τ₁) σ₂) σ₁ := by
  unfold ss
  rw [Finset.mul_sum (s := range (σ₁.length + 1))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum (s := range (σ₂.length + 1)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

theorem W1B_eq (σ τ ρ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => (-1 : ℚ) ^ τ₁.length *
      (ss (fun s₁ s₂ => ss (fun a b => Pw s₁.length b.length *
          (ff s₂.length * ff a.length * I ((d₁ : ℤ) < s₂.sum + a.sum))) τ₁) σ₂ *
        (((τ₂.length + ρ₂.length).choose τ₂.length : ℚ) *
          ss (fun u₁ u₂ => ss (fun v₁ v₂ => Pw u₁.length v₁.length *
            (((u₂.length + v₂.length).choose u₂.length : ℚ) *
              ff (u₂.length + v₂.length + (τ₂.length + ρ₂.length + 1)) *
              I ((d₂ : ℤ) < u₂.sum + v₂.sum +
                ((σ₂.sum + τ₁.sum - d₁) + (τ₂.sum + ρ₂.sum))))) ρ₁) σ₁))) ρ) τ) σ =
    ss (fun σa σb => ss (fun τp τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      Pw σa.length ρa.length * (ff σb.length * ff τp.length * ff τs.length * ff ρb.length) *
      (I ((d₁ : ℤ) < σb.sum + τp.sum) *
        I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum))) ρ) τ) σ := by
  -- Step A: the ρ-sum inside the σ₁-split
  rw [ss_ext σ fun σ₁ σ₂ => ss_ext τ fun τ₁ τ₂ => rearr_A1 _ _
    (fun ρ₂ => ((τ₂.length + ρ₂.length).choose τ₂.length : ℚ))
    (fun u₁ u₂ ρ₂ v₁ v₂ => Pw u₁.length v₁.length *
      (((u₂.length + v₂.length).choose u₂.length : ℚ) *
        ff (u₂.length + v₂.length + (τ₂.length + ρ₂.length + 1)) *
        I ((d₂ : ℤ) < u₂.sum + v₂.sum + ((σ₂.sum + τ₁.sum - d₁) + (τ₂.sum + ρ₂.sum))))) σ₁ ρ]
  -- Step B: Lemma 3(b) on ρ
  have hθ : ∀ σ₂ τ₁ τ₂ u₁ u₂ : List ℤ,
      ss (fun ρ₁ ρ₂ => ss (fun v₁ v₂ => ((τ₂.length + ρ₂.length).choose τ₂.length : ℚ) *
        (Pw u₁.length v₁.length * (((u₂.length + v₂.length).choose u₂.length : ℚ) *
          ff (u₂.length + v₂.length + (τ₂.length + ρ₂.length + 1)) *
          I ((d₂ : ℤ) < u₂.sum + v₂.sum + ((σ₂.sum + τ₁.sum - d₁) + (τ₂.sum + ρ₂.sum)))))) ρ₁) ρ =
      ss (fun a b => Pw u₁.length a.length * (ff (u₂.length + τ₂.length + 1) * ff b.length) *
        I (((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + τ₁.sum + τ₂.sum + b.sum)) ρ := by
    intro σ₂ τ₁ τ₂ u₁ u₂
    refine thetaB _ (fun y => Pw u₁.length y.length)
      (fun s => I (((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + τ₁.sum + τ₂.sum + s))
      u₂.length τ₂.length (fun y₁ y₂ z => ?_) ρ
    rw [I_iff (show (d₂ : ℤ) < u₂.sum + y₂.sum + ((σ₂.sum + τ₁.sum - d₁) + (τ₂.sum + z.sum)) ↔
      ((d₁ + d₂ : ℕ) : ℤ) < u₂.sum + σ₂.sum + τ₁.sum + τ₂.sum + (y₂.sum + z.sum) by
        push_cast; omega)]
    rw [show u₂.length + y₂.length + (τ₂.length + z.length + 1) =
      u₂.length + τ₂.length + (y₂.length + z.length) + 1 by omega]
    ring
  simp only [hθ]
  -- Step C: expand the first factor and collapse σ, τ (Lemma 3(c))
  rw [ss_ext σ fun σ₁ σ₂ => ss_ext τ fun τ₁ τ₂ => rearr_C _ _ _ σ₂ τ₁ σ₁]
  rw [sigTau (L := fun x s => ss (fun ρa ρb => Pw x.length ρa.length * ff ρb.length *
    I (((d₁ + d₂ : ℕ) : ℤ) < s + τ.sum + ρb.sum)) ρ) (d := d₁)]
  · refine ss_ext _ fun σa σb => ss_ext _ fun τp τs => ?_
    rw [ss_mul_left]
    refine ss_ext _ fun ρa ρb => ?_
    ring
  · intro σ₁ σ₂ τ₁ τ₂ x₁ x₂ s₁ s₂ a b hτ _ hs hab
    subst hτ hs hab
    rw [ss_mul_left, ss_mul_left]
    refine ss_ext _ fun ρa ρb => ?_
    simp only [List.sum_append, List.length_append, add_assoc, pow_add]
    ring

end TSI
```

### `TsiII2.lean`

```lean
import TsiII1

/-! # Identity (ii): the (B)-part of the terms of the second kind -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem choose_swap (a b : ℕ) : (a + b).choose a = (b + a).choose b := by
  rw [Nat.add_comm, Nat.choose_symm_add]

theorem rearr_B2 (c : List ℤ → ℚ) (S : List ℤ → List ℤ → ℚ) (k : List ℤ → List ℤ → ℚ)
    (B : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ)
    (σ τ ρ : List ℤ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => c τ₁ * (S τ₂ ρ₂ * (k σ₂ τ₁ *
      ss (fun u₁ u₂ => ss (fun v₁ v₂ => B σ₂ τ₁ τ₂ ρ₂ u₁ u₂ v₁ v₂) ρ₁) σ₁))) ρ) τ) σ =
    ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => c τ₁ * S τ₂ ρ₂ * ss (fun v₁ v₂ => ss (fun σ₁ σ₂ =>
      ss (fun u₁ u₂ => k σ₂ τ₁ * B σ₂ τ₁ τ₂ ρ₂ u₁ u₂ v₁ v₂) σ₁) σ) ρ₁) ρ) τ := by
  unfold ss
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem rearr_C2 (c : ℚ) (F : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (Y : List ℤ → List ℤ → ℚ)
    (τ₂ ρ₂ ρ₁ : List ℤ) :
    c * ss (fun t₁ t₂ => ss (F t₁ t₂) ρ₂) τ₂ * ss Y ρ₁ =
      ss (fun t₁ t₂ => ss (fun y₁ y₂ => ss (fun r₁ r₂ => c * F t₁ t₂ r₁ r₂ * Y y₁ y₂) ρ₂) ρ₁) τ₂ := by
  unfold ss
  rw [Finset.mul_sum (s := range (τ₂.length + 1)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum (s := range (ρ₁.length + 1))]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

theorem W2B_eq (σ τ ρ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => (-1 : ℚ) ^ τ₁.length *
      (ss (fun t₁ t₂ => ss (fun r₁ r₂ => Pw t₁.length r₁.length *
          (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂ *
        (((σ₂.length + τ₁.length).choose σ₂.length : ℚ) *
          ss (fun u₁ u₂ => ss (fun v₁ v₂ => Pw u₁.length v₁.length *
            (((u₂.length + v₂.length).choose u₂.length : ℚ) *
              ff (u₂.length + v₂.length + (σ₂.length + τ₁.length + 1)) *
              I ((d₁ : ℤ) < u₂.sum + v₂.sum +
                ((τ₂.sum + ρ₂.sum - d₂) + (σ₂.sum + τ₁.sum))))) ρ₁) σ₁))) ρ) τ) σ =
    ss (fun σa σb => ss (fun τp τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      Pw σa.length ρa.length * (ff σb.length * ff τp.length * ff τs.length * ff ρb.length) *
      (I ((d₂ : ℤ) < τs.sum + ρb.sum) *
        I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum))) ρ) τ) σ := by
  rw [rearr_B2 (fun τ₁ => (-1 : ℚ) ^ τ₁.length)
    (fun τ₂ ρ₂ => ss (fun t₁ t₂ => ss (fun r₁ r₂ => Pw t₁.length r₁.length *
      (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂)
    (fun σ₂ τ₁ => ((σ₂.length + τ₁.length).choose σ₂.length : ℚ))
    (fun σ₂ τ₁ τ₂ ρ₂ u₁ u₂ v₁ v₂ => Pw u₁.length v₁.length *
      (((u₂.length + v₂.length).choose u₂.length : ℚ) *
        ff (u₂.length + v₂.length + (σ₂.length + τ₁.length + 1)) *
        I ((d₁ : ℤ) < u₂.sum + v₂.sum + ((τ₂.sum + ρ₂.sum - d₂) + (σ₂.sum + τ₁.sum)))))]
  -- Lemma 3(b) on σ
  have hθ : ∀ τ₁ τ₂ ρ₂ v₁ v₂ : List ℤ,
      ss (fun σ₁ σ₂ => ss (fun u₁ u₂ => ((σ₂.length + τ₁.length).choose σ₂.length : ℚ) *
        (Pw u₁.length v₁.length * (((u₂.length + v₂.length).choose u₂.length : ℚ) *
          ff (u₂.length + v₂.length + (σ₂.length + τ₁.length + 1)) *
          I ((d₁ : ℤ) < u₂.sum + v₂.sum + ((τ₂.sum + ρ₂.sum - d₂) + (σ₂.sum + τ₁.sum)))))) σ₁) σ =
      ss (fun a b => Pw a.length v₁.length * (ff (v₂.length + τ₁.length + 1) * ff b.length) *
        I (((d₁ + d₂ : ℕ) : ℤ) < b.sum + v₂.sum + τ₁.sum + τ₂.sum + ρ₂.sum)) σ := by
    intro τ₁ τ₂ ρ₂ v₁ v₂
    refine thetaB _ (fun y => Pw y.length v₁.length)
      (fun s => I (((d₁ + d₂ : ℕ) : ℤ) < s + v₂.sum + τ₁.sum + τ₂.sum + ρ₂.sum))
      v₂.length τ₁.length (fun y₁ y₂ z => ?_) σ
    rw [I_iff (show (d₁ : ℤ) < y₂.sum + v₂.sum + ((τ₂.sum + ρ₂.sum - d₂) + (z.sum + τ₁.sum)) ↔
      ((d₁ + d₂ : ℕ) : ℤ) < (y₂.sum + z.sum) + v₂.sum + τ₁.sum + τ₂.sum + ρ₂.sum by
        push_cast; omega)]
    rw [show y₂.length + v₂.length + (z.length + τ₁.length + 1) =
      v₂.length + τ₁.length + (y₂.length + z.length) + 1 by omega,
      choose_swap z.length τ₁.length, choose_swap y₂.length v₂.length]
    ring
  simp only [hθ]
  rw [ss_ext τ fun τ₁ τ₂ => ss_ext ρ fun ρ₁ ρ₂ => rearr_C2 _ _ _ τ₂ ρ₂ ρ₁]
  rw [rhoTau (L := fun y s => ss (fun σa σb => Pw σa.length y.length * ff σb.length *
    I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + s)) σ) (d := d₂)]
  · have e : ∀ τp τs ρa ρb : List ℤ, (-1 : ℚ) ^ τp.length * ff τp.length *
        (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
        ss (fun σa σb => Pw σa.length ρa.length * ff σb.length *
          I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum)) σ =
        ss (fun σa σb => (-1 : ℚ) ^ τp.length * Pw σa.length ρa.length *
          (ff σb.length * ff τp.length * ff τs.length * ff ρb.length) *
          (I ((d₂ : ℤ) < τs.sum + ρb.sum) *
            I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum))) σ := by
      intro τp τs ρa ρb
      rw [ss_mul_left]
      exact ss_ext _ fun σa σb => by ring
    exact (ss_ext τ fun τp τs => (ss_ext ρ fun ρa ρb => e τp τs ρa ρb).trans
      (ss_comm _ ρ σ)).trans (ss_comm _ τ σ)
  · intro τ₁ τ₂ ρ₁ ρ₂ t₁ t₂ y₁ y₂ r₁ r₂ hτ ht hy hr
    subst hτ ht hy hr
    rw [ss_mul_left, ss_mul_left]
    refine ss_ext _ fun σa σb => ?_
    simp only [List.sum_append, List.length_append]
    ring_nf

end TSI
```

### `TsiIIA.lean`

```lean
import TsiII2

/-! # Identity (ii): the (A)-parts -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

theorem ss3_mul_right (P : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (c : ℚ)
    (X Y Z : List ℤ) :
    ss (fun a b => ss (fun e f => ss (fun g h => P a b e f g h * c) Z) Y) X =
      ss (fun a b => ss (fun e f => ss (P a b e f) Z) Y) X * c := by
  rw [ss_mul_right]
  exact ss_ext _ fun a b => ss2_mul_right _ _ _ _ |>.symm ▸ rfl

theorem prodA (c k : ℚ) (F : List ℤ → List ℤ → List ℤ → List ℤ → ℚ)
    (G : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (x y z w : List ℤ) :
    c * (ss (fun s₁ s₂ => ss (F s₁ s₂) y) x * (k * ss (fun t₁ t₂ => ss (G t₁ t₂) w) z)) =
      ss (fun s₁ s₂ => ss (fun a b => ss (fun t₁ t₂ => ss (fun r₁ r₂ =>
        c * F s₁ s₂ a b * (k * G t₁ t₂ r₁ r₂)) w) z) y) x := by
  rw [show c * (ss (fun s₁ s₂ => ss (F s₁ s₂) y) x * (k * ss (fun t₁ t₂ => ss (G t₁ t₂) w) z)) =
    ss (fun s₁ s₂ => ss (F s₁ s₂) y) x * ss (fun t₁ t₂ => ss (G t₁ t₂) w) z * (c * k) by ring,
    prod_ss2, ss_mul_right]
  refine ss_ext _ fun _ _ => ?_
  rw [ss_mul_right]
  refine ss_ext _ fun _ _ => ?_
  rw [ss_mul_right]
  refine ss_ext _ fun _ _ => ?_
  rw [ss_mul_right]
  exact ss_ext _ fun _ _ => by ring

theorem prodA' (c k : ℚ) (F : List ℤ → List ℤ → List ℤ → List ℤ → ℚ)
    (G : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) (x y z w : List ℤ) :
    c * (ss (fun t₁ t₂ => ss (G t₁ t₂) w) z * (k * ss (fun s₁ s₂ => ss (F s₁ s₂) y) x)) =
      ss (fun s₁ s₂ => ss (fun a b => ss (fun t₁ t₂ => ss (fun r₁ r₂ =>
        c * F s₁ s₂ a b * (k * G t₁ t₂ r₁ r₂)) w) z) y) x := by
  rw [← prodA]
  ring

/-- Regrouping of the splits for the (A)-parts. -/
theorem permA (Z : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ →
      List ℤ → List ℤ → ℚ) (σ τ ρ : List ℤ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => ss (fun s₁ s₂ => ss (fun a b =>
      ss (fun t₁ t₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) τ₂) τ₁) σ₂) ρ) τ) σ =
    ss (fun σa s₂ => ss (fun a R => ss (fun M t₂ => ss (fun ρa r₂ => ss (fun σ₁ s₁ =>
      ss (fun b t₁ => ss (fun ρ₁ r₁ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρa) M) σa) ρ) R) τ) σ := by
  calc _ = ss (fun σ₁ σ₂ => ss (fun s₁ s₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => ss (fun a b =>
        ss (fun t₁ t₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) τ₂) τ₁) ρ) τ) σ₂) σ :=
        ss_ext σ fun σ₁ σ₂ => (ss_ext τ fun τ₁ τ₂ => ss_comm _ ρ σ₂).trans (ss_comm _ τ σ₂)
    _ = ss (fun σ₁ σ₂ => ss (fun s₁ s₂ => ss (fun τ₁ τ₂ => ss (fun a b => ss (fun t₁ t₂ =>
        ss (fun ρ₁ ρ₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) ρ) τ₂) τ₁) τ) σ₂) σ :=
        ss_ext σ fun σ₁ σ₂ => ss_ext σ₂ fun s₁ s₂ => ss_ext τ fun τ₁ τ₂ =>
          (ss_comm _ ρ τ₁).trans (ss_ext τ₁ fun a b => ss_comm _ ρ τ₂)
    _ = ss (fun σa s₂ => ss (fun σ₁ s₁ => ss (fun τ₁ τ₂ => ss (fun a b => ss (fun t₁ t₂ =>
        ss (fun ρ₁ ρ₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) ρ) τ₂) τ₁) τ) σa) σ :=
        ss_coassoc (fun σ₁ s₁ s₂ => ss (fun τ₁ τ₂ => ss (fun a b => ss (fun t₁ t₂ =>
          ss (fun ρ₁ ρ₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) ρ) τ₂) τ₁) τ) σ
    _ = ss (fun σa s₂ => ss (fun σ₁ s₁ => ss (fun a R => ss (fun M t₂ => ss (fun b t₁ =>
        ss (fun ρ₁ ρ₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) ρ) M) R) τ) σa) σ :=
        ss_ext σ fun σa s₂ => ss_ext σa fun σ₁ s₁ => ss4 (fun a b t₁ t₂ =>
          ss (fun ρ₁ ρ₂ => ss (fun r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ₂) ρ) τ
    _ = ss (fun σa s₂ => ss (fun σ₁ s₁ => ss (fun a R => ss (fun M t₂ => ss (fun b t₁ =>
        ss (fun ρa r₂ => ss (fun ρ₁ r₁ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρa) ρ) M) R) τ) σa) σ :=
        ss_ext σ fun σa s₂ => ss_ext σa fun σ₁ s₁ => ss_ext τ fun a R => ss_ext R fun M t₂ =>
          ss_ext M fun b t₁ => ss_coassoc (fun ρ₁ r₁ r₂ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρ
    _ = ss (fun σa s₂ => ss (fun a R => ss (fun M t₂ => ss (fun σ₁ s₁ => ss (fun b t₁ =>
        ss (fun ρa r₂ => ss (fun ρ₁ r₁ => Z σ₁ ρ₁ s₁ s₂ a b t₁ t₂ r₁ r₂) ρa) ρ) M) σa) R) τ) σ :=
        ss_ext σ fun σa s₂ => (ss_comm _ σa τ).trans (ss_ext τ fun a R => ss_comm _ σa R)
    _ = _ :=
        ss_ext σ fun σa s₂ => ss_ext τ fun a R => ss_ext R fun M t₂ =>
          (ss_ext σa fun σ₁ s₁ => ss_comm _ M ρ).trans (ss_comm _ σa ρ)

theorem W1A_eq (σ τ ρ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => (-1 : ℚ) ^ τ₁.length *
      (ss (fun s₁ s₂ => ss (fun a b => Pw s₁.length b.length *
          (ff s₂.length * ff a.length * I ((d₁ : ℤ) < s₂.sum + a.sum))) τ₁) σ₂ *
        (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
          ss (fun t₁ t₂ => ss (fun r₁ r₂ => ((t₁.length + r₁.length).choose t₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (t₁.length + r₁.length + 1)) *
            (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂))) ρ) τ) σ =
    ss (fun σa σb => ss (fun τp R => ss (fun τm τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      H1 σa.length τm.length ρa.length) ρ) R) τ) σ := by
  have e1 : ∀ σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂ : List ℤ, (-1 : ℚ) ^ τ₁.length *
      (ss (fun s₁ s₂ => ss (fun a b => Pw s₁.length b.length *
          (ff s₂.length * ff a.length * I ((d₁ : ℤ) < s₂.sum + a.sum))) τ₁) σ₂ *
        (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
          ss (fun t₁ t₂ => ss (fun r₁ r₂ => ((t₁.length + r₁.length).choose t₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (t₁.length + r₁.length + 1)) *
            (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂)) =
      ss (fun s₁ s₂ => ss (fun a b => ss (fun t₁ t₂ => ss (fun r₁ r₂ =>
        ((-1 : ℚ) ^ b.length * Pw s₁.length b.length *
          (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
            ((t₁.length + r₁.length).choose t₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (t₁.length + r₁.length + 1)))) *
        ((-1 : ℚ) ^ a.length * (ff s₂.length * ff a.length * I ((d₁ : ℤ) < s₂.sum + a.sum)) *
          (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum)))) ρ₂) τ₂) τ₁) σ₂ := by
    intro σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂
    rw [prodA]
    exact ss_ext _ fun s₁ s₂ => ss_congr fun a b hab => by
      subst hab
      exact ss_ext _ fun t₁ t₂ => ss_ext _ fun r₁ r₂ => by
        rw [List.length_append, pow_add]
        ring
  simp only [e1]
  rw [permA]
  refine ss_ext _ fun σa σb => ss_ext _ fun τp R => ss_ext _ fun τm τs => ss_ext _ fun ρa ρb => ?_
  rw [ss3_mul_right, coll_H1]
  ring

theorem W2A_eq (σ τ ρ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => (-1 : ℚ) ^ τ₁.length *
      (ss (fun t₁ t₂ => ss (fun r₁ r₂ => Pw t₁.length r₁.length *
          (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂ *
        (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
          ss (fun s₁ s₂ => ss (fun r₁ r₂ => ((s₁.length + r₁.length).choose s₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (s₁.length + r₁.length + 1)) *
            (ff s₂.length * ff r₂.length * I ((d₁ : ℤ) < s₂.sum + r₂.sum))) τ₁.reverse) σ₂))) ρ) τ) σ =
    ss (fun σa σb => ss (fun τp R => ss (fun τm τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      H2 σa.length τm.length ρa.length) ρ) R) τ) σ := by
  have e1 : ∀ σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂ : List ℤ, (-1 : ℚ) ^ τ₁.length *
      (ss (fun t₁ t₂ => ss (fun r₁ r₂ => Pw t₁.length r₁.length *
          (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum))) ρ₂) τ₂ *
        (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
          ss (fun s₁ s₂ => ss (fun r₁ r₂ => ((s₁.length + r₁.length).choose s₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (s₁.length + r₁.length + 1)) *
            (ff s₂.length * ff r₂.length * I ((d₁ : ℤ) < s₂.sum + r₂.sum))) τ₁.reverse) σ₂)) =
      ss (fun s₁ s₂ => ss (fun a b => ss (fun t₁ t₂ => ss (fun r₁ r₂ =>
        ((-1 : ℚ) ^ b.length * Pw t₁.length r₁.length *
          (((σ₁.length + ρ₁.length).choose σ₁.length : ℚ) *
            ((s₁.length + b.length).choose s₁.length : ℚ) *
            bb (σ₁.length + ρ₁.length + (s₁.length + b.length + 1)))) *
        ((-1 : ℚ) ^ a.length * (ff s₂.length * ff a.length * I ((d₁ : ℤ) < s₂.sum + a.sum)) *
          (ff t₂.length * ff r₂.length * I ((d₂ : ℤ) < t₂.sum + r₂.sum)))) ρ₂) τ₂) τ₁) σ₂ := by
    intro σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂
    rw [ss_ext σ₂ fun s₁ s₂ => ss_reverse _ τ₁]
    rw [prodA']
    exact ss_ext _ fun s₁ s₂ => ss_congr fun a b hab => by
      subst hab
      exact ss_ext _ fun t₁ t₂ => ss_ext _ fun r₁ r₂ => by
        simp only [List.length_append, List.length_reverse, List.sum_reverse, pow_add]
        ring
  simp only [e1]
  rw [permA]
  refine ss_ext _ fun σa σb => ss_ext _ fun τp R => ss_ext _ fun τm τs => ss_ext _ fun ρa ρb => ?_
  rw [ss3_mul_right, coll_H2]
  ring

end TSI
```

### `TsiWII.lean`

```lean
import TsiIIA
import TsiMainI

/-! # Identity (ii) in cut form: the total vanishes for `τ ≠ ∅` -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- The summand of (ii) in cut form, with `ρ = rev ϑ`, divided by `(-1)^{ℓϑ}`. -/
noncomputable def V (d₁ d₂ : ℕ) (σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂ : List ℤ) : ℚ :=
  (-1 : ℚ) ^ τ₁.length * (Sh (nu d₁) σ₂ τ₁.reverse *
      Sh (fun X => Sh (fun N => nu d₂ (X ++ (σ₂.sum + τ₁.sum - d₁) :: N)) τ₂ ρ₂) σ₁ ρ₁) +
    (-1 : ℚ) ^ τ₁.length * (Sh (nu d₂) τ₂ ρ₂ *
      Sh (fun X => Sh (fun M => nu d₁ (X ++ (τ₂.sum + ρ₂.sum - d₂) :: M)) σ₂ τ₁.reverse) σ₁ ρ₁)

/-- `∑_{τ=(τp,τs)} (-1)^{ℓτp}/(ℓτp! ℓτs!) · P = 0` for `τ ≠ ∅`. -/
theorem alt_zero (σ τ ρ : List ℤ) (hτ : τ ≠ []) (P : List ℤ → List ℤ → List ℤ → List ℤ → ℚ) :
    ss (fun σa σb => ss (fun τp τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length * ff τp.length *
      ff τs.length * P σa σb ρa ρb) ρ) τ) σ = 0 := by
  rw [← ss_zero σ]
  refine ss_ext _ fun σa σb => ?_
  rw [ss_comm, ← ss_zero ρ]
  refine ss_ext _ fun ρa ρb => ?_
  rw [← ss_mul_right, coll_alt τ hτ, zero_mul]

theorem WA_sum (σ τ ρ : List ℤ) (d₁ d₂ : ℕ) :
    ss (fun σa σb => ss (fun τp R => ss (fun τm τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      H1 σa.length τm.length ρa.length) ρ) R) τ) σ +
    ss (fun σa σb => ss (fun τp R => ss (fun τm τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      H2 σa.length τm.length ρa.length) ρ) R) τ) σ =
    -ss (fun σa σb => ss (fun τp τs => ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      Pw σa.length ρa.length) ρ) τ) σ := by
  rw [← ss_add, ← ss_neg]
  refine ss_ext _ fun σa σb => ?_
  rw [← ss_add, ← ss_neg]
  refine ss_ext _ fun τp R => ?_
  rw [← ss_add]
  refine Eq.trans ?_ (ss_nil_of_len (g := fun τm τs => -ss (fun ρa ρb => (-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum)) *
      Pw σa.length ρa.length) ρ) R)
  refine ss_ext _ fun τm τs => ?_
  rw [← ss_add]
  split_ifs with h
  · rw [← ss_neg]
    refine ss_ext _ fun ρa ρb => ?_
    have hz' := H_zero σa.length τm.length ρa.length
    simp only [H3, h, ↓reduceIte] at hz'
    rw [h]
    unfold Pw
    linear_combination ((-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum))) * hz'
  · rw [← ss_zero ρ]
    refine ss_ext _ fun ρa ρb => ?_
    have hz' := H_zero σa.length τm.length ρa.length
    simp only [H3, h, ↓reduceIte, add_zero] at hz'
    linear_combination ((-1 : ℚ) ^ τp.length *
      (ff σb.length * ff τp.length * I ((d₁ : ℤ) < σb.sum + τp.sum)) *
      (ff τs.length * ff ρb.length * I ((d₂ : ℤ) < τs.sum + ρb.sum))) * hz'

theorem W_zero (σ τ ρ : List ℤ) (hτ : τ ≠ []) (d₁ d₂ : ℕ) :
    ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ => ss (fun ρ₁ ρ₂ => V d₁ d₂ σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂) ρ) τ) σ = 0 := by
  unfold V
  simp only [Sh_nu_rev]
  simp only [Sh_nu, Sh_split_ii, List.length_reverse, List.sum_reverse, mul_add, ss_add]
  rw [W1B_eq, W1A_eq, W2B_eq, W2A_eq]
  rw [show ∀ a b c e : ℚ, a + b + (c + e) = a + c + (b + e) from fun a b c e => by ring, WA_sum]
  simp only [← ss_add, ← ss_neg]
  rw [← alt_zero σ τ ρ hτ (fun σa σb ρa ρb => Pw σa.length ρa.length * ff σb.length *
    ff ρb.length * I (((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum))]
  refine ss_ext _ fun σa σb => ss_congr fun τp τs hτs => ss_ext _ fun ρa ρb => ?_
  have Br := bracket d₁ d₂ (σb.sum + τp.sum) (τs.sum + ρb.sum)
  rw [I_iff (show ((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τp.sum + (τs.sum + ρb.sum) ↔
    ((d₁ + d₂ : ℕ) : ℤ) < σb.sum + τ.sum + ρb.sum by
      rw [← hτs, List.sum_append]; constructor <;> intro h <;> linarith)] at Br
  linear_combination (-((-1 : ℚ) ^ τp.length * Pw σa.length ρa.length *
    (ff σb.length * ff τp.length * ff τs.length * ff ρb.length))) * Br

end TSI
```

### `TsiMainII.lean`

```lean
import TsiWII

/-! # Definition A.5(ii) for the uri multiplicities, `τ ≠ ∅` -/

set_option linter.unusedSimpArgs false

namespace TSI

open Finset

/-- **Definition A.5(ii) holds for the uri multiplicities whenever `τ ≠ ∅`** (Conjecture A.7,
part (ii); the case `τ = ∅` is false as printed, see `tsi_ii_tau_nil_false`). -/
theorem tsi_ii (σ τ ϑ : List ℤ) (hσ : IsComp σ) (hτ : IsComp τ) (hϑ : IsComp ϑ) (hτne : τ ≠ [])
    (d₁ d₂ : ℕ) : TSI_ii B1 σ τ ϑ d₁ d₂ := by
  have hσ' := isComp_nonneg hσ
  have hτ' := isComp_nonneg hτ
  have hϑ' := isComp_nonneg hϑ
  unfold TSI_ii
  simp only [muF_sh_rev, muF_cat_ii]
  rw [muB_B1]
  symm
  refine Eq.trans ?_ (show (-1 : ℚ) ^ ϑ.length * ss (fun σ₁ σ₂ => ss (fun τ₁ τ₂ =>
      ss (fun ρ₁ ρ₂ => V d₁ d₂ σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂) ϑ.reverse) τ) σ = 0 by
    rw [W_zero σ τ ϑ.reverse hτne d₁ d₂, mul_zero])
  rw [ss_ext σ fun σ₁ σ₂ => ss_ext τ fun τ₁ τ₂ => ss_reverse _ ϑ]
  unfold ss
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => ?_
  have es := List.sum_take_add_sum_drop σ i
  have et := List.sum_take_add_sum_drop τ k
  have eϑ := List.sum_take_add_sum_drop ϑ j
  have h1 := term_ii (p := σ.drop i) (q := (τ.take k).reverse) (u := σ.take i)
    (v := (ϑ.drop j).reverse) (x := τ.drop k) (y := (ϑ.take j).reverse)
    (nonneg_drop hσ' i) (nonneg_reverse (nonneg_take hτ' k)) (nonneg_take hσ' i)
    (nonneg_reverse (nonneg_drop hϑ' j)) (nonneg_drop hτ' k) (nonneg_reverse (nonneg_take hϑ' j))
    d₁ d₂ (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
    (by simp only [List.sum_reverse]; linarith)
  have h2 := term_ii (p := τ.drop k) (q := (ϑ.take j).reverse) (u := σ.take i)
    (v := (ϑ.drop j).reverse) (x := σ.drop i) (y := (τ.take k).reverse)
    (nonneg_drop hτ' k) (nonneg_reverse (nonneg_take hϑ' j)) (nonneg_take hσ' i)
    (nonneg_reverse (nonneg_drop hϑ' j)) (nonneg_drop hσ' i) (nonneg_reverse (nonneg_take hτ' k))
    d₂ d₁ (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
    (by simp only [List.sum_reverse]; linarith)
  have hm : (-1 : ℚ) ^ ϑ.length = (-1 : ℚ) ^ (ϑ.take j).length * (-1 : ℚ) ^ (ϑ.drop j).length := by
    rw [← pow_add, ← List.length_append, List.take_append_drop]
  simp only [List.sum_reverse] at h1 h2
  rw [hm]
  unfold V
  simp only [List.sum_reverse, List.reverse_reverse]
  linear_combination ((-1 : ℚ) ^ (τ.take k).length * (-1 : ℚ) ^ (ϑ.drop j).length *
      (-1 : ℚ) ^ (ϑ.take j).length) * h1 +
    ((-1 : ℚ) ^ (ϑ.take j).length * (-1 : ℚ) ^ (ϑ.drop j).length *
      (-1 : ℚ) ^ (τ.take k).length) * h2

end TSI
```

### `TsiEnd.lean`

```lean
import TsiMainII
import TsiExamples

/-! # Endpoints for MathDB 368177 (Burmester–Kühn, arXiv:2504.19661, Conjecture A.7) -/

namespace TSI

/-- Conjecture A.7: the uri multiplicities of Definition 5.3 satisfy the threshold shuffle
identities of Definition A.5 — identity (i) for all compositions `σ, ϑ` and all `d₁, d₂ ≥ 0`,
and identity (ii) for all compositions `σ, τ, ϑ` with `τ ≠ ∅` and all `d₁, d₂ ≥ 0`. -/
theorem conjecture_A7 :
    (∀ σ ϑ : List ℤ, IsComp σ → IsComp ϑ → ∀ d₁ d₂ : ℕ, TSI_i B1 σ ϑ d₁ d₂) ∧
    (∀ σ τ ϑ : List ℤ, IsComp σ → IsComp τ → IsComp ϑ → τ ≠ [] →
      ∀ d₁ d₂ : ℕ, TSI_ii B1 σ τ ϑ d₁ d₂) :=
  ⟨fun σ ϑ hσ hϑ d₁ d₂ => tsi_i σ ϑ hσ hϑ d₁ d₂,
    fun σ τ ϑ hσ hτ hϑ hτne d₁ d₂ => tsi_ii σ τ ϑ hσ hτ hϑ hτne d₁ d₂⟩

/-- The literal (ii) with `τ = ∅` fails for the uri multiplicities themselves. -/
theorem tsi_ii_tau_nil_false_uri : ¬ TSI_ii B1 [] [] [1] 0 0 :=
  tsi_ii_tau_nil_false B1 B1_one_one

end TSI

#print axioms TSI.conjecture_A7
#print axioms TSI.tsi_i
#print axioms TSI.tsi_ii
#print axioms TSI.tsi_ii_tau_nil_false
#print axioms TSI.tsi_ii_tau_nil_false_uri
#print axioms TSI.example_A6_i
#print axioms TSI.example_A6_ii
```

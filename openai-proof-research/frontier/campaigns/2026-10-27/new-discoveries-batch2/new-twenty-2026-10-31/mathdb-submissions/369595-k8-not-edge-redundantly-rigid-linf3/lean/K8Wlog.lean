import K8Comb
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Symmetry breaking

The isometries of `ℓ∞³` used here are coordinate permutations and coordinate
reflections; together with a relabelling of the vertices they preserve `Good`
(`good_transform`).  Every good placement can be transformed into an anchored
one (`exists_anchored`):

* the singleton cut `{0}` forces at least two edges of each colour at vertex `0`;
  since `0` has seven edges, some colour has at least three;
* permute coordinates so that this colour is coordinate `0`;
* among three neighbours of colour `0`, two have the same orientation; reflect
  coordinate `0` if necessary so that they lie above vertex `0`;
* reflect coordinates `1` and `2` so that one neighbour of each lies above `0`;
* relabel the vertices.
-/

namespace K8

open Classical

variable {p : Fin 8 → Fin 3 → ℝ}

/-- The transformed placement: relabel vertices by `σ`, permute coordinates by
`τ`, multiply coordinate `c` by `ε c`. -/
def transform (p : Fin 8 → Fin 3 → ℝ) (σ : Equiv.Perm (Fin 8)) (τ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → ℝ) : Fin 8 → Fin 3 → ℝ :=
  fun v c => ε c * p (σ v) (τ c)

theorem dom_transform {σ : Equiv.Perm (Fin 8)} {τ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ}
    (hε : ∀ c, |ε c| = 1) {a b : Fin 8} {k : Fin 3} (h : Dom (p (σ b) - p (σ a)) (τ k)) :
    Dom (transform p σ τ ε b - transform p σ τ ε a) k := by
  intro j hj
  have hj' : τ j ≠ τ k := fun e => hj (τ.injective e)
  have := h (τ j) hj'
  simp only [Pi.sub_apply, transform]
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, hε, hε, one_mul, one_mul]
  simpa using this

theorem good_transform (hg : Good p) (σ : Equiv.Perm (Fin 8)) (τ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → ℝ) (hε : ∀ c, |ε c| = 1) : Good (transform p σ τ ε) where
  dom u v huv := by
    obtain ⟨k, hk⟩ := hg.dom (σ u) (σ v) (fun e => huv (σ.injective e))
    refine ⟨τ.symm k, dom_transform hε ?_⟩
    simpa using hk
  cut u v huv S k hS hS' := by
    obtain ⟨a0, ha0⟩ := hS
    obtain ⟨b0, hb0⟩ := hS'
    obtain ⟨a, ha, b, hb, h1, h2, hd⟩ := hg.cut (σ u) (σ v) (fun e => huv (σ.injective e))
      (S.map σ.toEmbedding) (τ k) ⟨σ a0, by simpa [Finset.mem_map_equiv] using ha0⟩
      ⟨σ b0, by simpa [Finset.mem_map_equiv] using hb0⟩
    rw [Finset.mem_map_equiv] at ha hb
    refine ⟨σ.symm a, ha, σ.symm b, hb, ?_, ?_, dom_transform hε ?_⟩
    · rintro ⟨rfl, rfl⟩; exact h1 ⟨by simp, by simp⟩
    · rintro ⟨rfl, rfl⟩; exact h2 ⟨by simp, by simp⟩
    · simpa using hd

theorem Dom.ne_zero3 {x : Fin 3 → ℝ} {k : Fin 3} (h : Dom x k) : x k ≠ 0 := by
  have : 0 < |x k| := by
    fin_cases k
    · exact h.pos 1 (by decide)
    · exact h.pos 0 (by decide)
    · exact h.pos 0 (by decide)
  exact abs_pos.mp this

/-- Two distinct neighbours of each colour at vertex `0`. -/
theorem two_of_colour (hg : Good p) (k : Fin 3) :
    ∃ b₁ b₂ : Fin 8, b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ b₁ ≠ b₂ ∧ Dom (p b₁ - p 0) k ∧ Dom (p b₂ - p 0) k := by
  obtain ⟨a, ha, b, hb, -, -, hd⟩ := hg.cut 0 1 (by decide) {0} k ⟨0, by simp⟩ ⟨1, by simp⟩
  rw [Finset.mem_singleton] at ha hb
  subst ha
  obtain ⟨a', ha', b', hb', h1, -, hd'⟩ := hg.cut 0 b (Ne.symm hb) {0} k ⟨0, by simp⟩ ⟨b, by simpa⟩
  rw [Finset.mem_singleton] at ha' hb'
  subst ha'
  exact ⟨b, b', hb, hb', fun e => h1 ⟨rfl, e.symm⟩, hd, hd'⟩

/-- Some colour has three distinct neighbours at vertex `0`. -/
theorem three_of_some_colour (hg : Good p) :
    ∃ k : Fin 3, ∃ a₁ a₂ a₃ : Fin 8, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
      Dom (p a₁ - p 0) k ∧ Dom (p a₂ - p 0) k ∧ Dom (p a₃ - p 0) k := by
  let N : Fin 3 → Finset (Fin 8) := fun k => Finset.univ.filter fun w => w ≠ 0 ∧ Dom (p w - p 0) k
  have hsub : Finset.univ.erase 0 ⊆ N 0 ∪ N 1 ∪ N 2 := by
    intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨k, hk⟩ := hg.dom 0 w (Ne.symm hw.1)
    simp only [N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k
    · exact Or.inl (Or.inl ⟨hw.1, hk⟩)
    · exact Or.inl (Or.inr ⟨hw.1, hk⟩)
    · exact Or.inr ⟨hw.1, hk⟩
  have h7 : (Finset.univ.erase (0 : Fin 8)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  have hle := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (N 0 ∪ N 1) (N 2)
  have hu2 := Finset.card_union_le (N 0) (N 1)
  have : ∃ k, 2 < (N k).card := by
    by_contra hno
    push Not at hno
    have := hno 0; have := hno 1; have := hno 2
    omega
  obtain ⟨k, hk⟩ := this
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hk
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂ h₃
  exact ⟨k, a₁, a₂, a₃, h₁.1, h₂.1, h₃.1, h12, h13, h23, h₁.2, h₂.2, h₃.2⟩

/-- The reflection sign making `w` lie above `z` in one coordinate. -/
noncomputable def upSign (z w : ℝ) : ℝ := if z < w then 1 else -1

theorem upSign_abs (z w : ℝ) : |upSign z w| = 1 := by
  unfold upSign; split <;> simp

theorem upSign_up {z w : ℝ} (h : w ≠ z) : upSign z w * z < upSign z w * w := by
  unfold upSign
  split
  · linarith
  · rcases lt_or_gt_of_ne h with h' | h'
    · linarith
    · contradiction

theorem upSign_up' {z w w' : ℝ} (h : w' ≠ z) (hiff : z < w ↔ z < w') :
    upSign z w * z < upSign z w * w' := by
  unfold upSign
  split
  · rename_i hw; have := hiff.mp hw; linarith
  · rename_i hw
    have : ¬ z < w' := fun h' => hw (hiff.mpr h')
    rcases lt_or_gt_of_ne h with h' | h'
    · linarith
    · contradiction

theorem exists_anchored (hg : Good p) : ∃ q, Good q ∧ Anchored q := by
  obtain ⟨k₀, a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, d1, d2, d3⟩ := three_of_some_colour hg
  -- two of the three have the same orientation in coordinate `k₀`
  have hpig : ∃ x y z : Fin 8, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Dom (p x - p 0) k₀ ∧ Dom (p y - p 0) k₀ ∧ Dom (p z - p 0) k₀ ∧
      (p 0 k₀ < p x k₀ ↔ p 0 k₀ < p y k₀) := by
    by_cases e12 : (p 0 k₀ < p a₁ k₀ ↔ p 0 k₀ < p a₂ k₀)
    · exact ⟨a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, d1, d2, d3, e12⟩
    by_cases e13 : (p 0 k₀ < p a₁ k₀ ↔ p 0 k₀ < p a₃ k₀)
    · exact ⟨a₁, a₃, a₂, h1, h3, h2, h13, h12, Ne.symm h23, d1, d3, d2, e13⟩
    · refine ⟨a₂, a₃, a₁, h2, h3, h1, h23, Ne.symm h12, Ne.symm h13, d2, d3, d1, ?_⟩
      tauto
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, dx, dy, dz, hiff⟩ := hpig
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 k₀
  have hτ0 : τ 0 = k₀ := Equiv.swap_apply_left 0 k₀
  have hτ1 : τ 1 ≠ k₀ := fun e => by
    have : τ 1 = τ 0 := by rw [e, hτ0]
    exact absurd (τ.injective this) (by decide)
  have hτ2 : τ 2 ≠ k₀ := fun e => by
    have : τ 2 = τ 0 := by rw [e, hτ0]
    exact absurd (τ.injective this) (by decide)
  have hτ12 : τ 1 ≠ τ 2 := fun e => absurd (τ.injective e) (by decide)
  obtain ⟨b₁, b₂, hb1, hb2, hb12, db1, db2⟩ := two_of_colour hg (τ 1)
  obtain ⟨c₁, c₂, hc1, hc2, hc12, dc1, dc2⟩ := two_of_colour hg (τ 2)
  -- distinctness across colours
  have dne : ∀ {u w : Fin 8} {k l : Fin 3}, Dom (p u - p 0) k → Dom (p w - p 0) l → k ≠ l →
      u ≠ w := by
    intro u w k l hu hw hkl e
    subst e
    exact hkl (hu.unique hw)
  let L : List (Fin 8) := [0, x, y, z, b₁, b₂, c₁, c₂]
  have hL : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨Ne.symm hx, Ne.symm hy, Ne.symm hz, Ne.symm hb1, Ne.symm hb2, Ne.symm hc1,
      Ne.symm hc2⟩, ⟨hxy, hxz, dne dx db1 (Ne.symm hτ1), dne dx db2 (Ne.symm hτ1),
      dne dx dc1 (Ne.symm hτ2), dne dx dc2 (Ne.symm hτ2)⟩,
      ⟨hyz, dne dy db1 (Ne.symm hτ1), dne dy db2 (Ne.symm hτ1), dne dy dc1 (Ne.symm hτ2),
      dne dy dc2 (Ne.symm hτ2)⟩,
      ⟨dne dz db1 (Ne.symm hτ1), dne dz db2 (Ne.symm hτ1), dne dz dc1 (Ne.symm hτ2),
      dne dz dc2 (Ne.symm hτ2)⟩,
      ⟨hb12, dne db1 dc1 hτ12, dne db1 dc2 hτ12⟩, ⟨dne db2 dc1 hτ12, dne db2 dc2 hτ12⟩, hc12, not_false⟩
  let f : Fin 8 → Fin 8 := ![0, x, y, z, b₁, b₂, c₁, c₂]
  have hf : Function.Injective f := by
    intro i j hij
    have hget : ∀ i : Fin 8, f i = L.get ⟨i, by simp [L]⟩ := by
      intro i; fin_cases i <;> rfl
    rw [hget, hget] at hij
    have := (List.Nodup.get_inj_iff hL).mp hij
    simpa using this
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : ∀ i, σ i = f i := fun _ => rfl
  let ε : Fin 3 → ℝ := ![upSign (p 0 k₀) (p x k₀), upSign (p 0 (τ 1)) (p b₁ (τ 1)),
    upSign (p 0 (τ 2)) (p c₁ (τ 2))]
  have hε : ∀ c, |ε c| = 1 := by
    intro c; fin_cases c <;> exact upSign_abs _ _
  refine ⟨transform p σ τ ε, good_transform hg σ τ ε hε, ?_⟩
  have hd : ∀ (i : Fin 8) (k : Fin 3), Dom (p (f i) - p 0) (τ k) →
      Dom (transform p σ τ ε i - transform p σ τ ε 0) k := by
    intro i k h
    apply dom_transform hε
    rw [hσ, hσ]; exact h
  have ne0 : ∀ {w : Fin 8} {k : Fin 3}, Dom (p w - p 0) k → p w k ≠ p 0 k := by
    intro w k h e
    exact h.ne_zero3 (by simp [e])
  constructor
  · exact hd 1 0 (by rw [hτ0]; exact dx)
  · exact hd 2 0 (by rw [hτ0]; exact dy)
  · exact hd 3 0 (by rw [hτ0]; exact dz)
  · exact hd 4 1 db1
  · exact hd 5 1 db2
  · exact hd 6 2 dc1
  · exact hd 7 2 dc2
  · show ε 0 * p (σ 0) (τ 0) < ε 0 * p (σ 1) (τ 0)
    rw [hσ, hσ, hτ0]
    exact upSign_up (ne0 dx)
  · show ε 0 * p (σ 0) (τ 0) < ε 0 * p (σ 2) (τ 0)
    rw [hσ, hσ, hτ0]
    exact upSign_up' (ne0 dy) hiff
  · show ε 1 * p (σ 0) (τ 1) < ε 1 * p (σ 4) (τ 1)
    rw [hσ, hσ]
    exact upSign_up (ne0 db1)
  · show ε 2 * p (σ 0) (τ 2) < ε 2 * p (σ 6) (τ 2)
    rw [hσ, hσ]
    exact upSign_up (ne0 dc1)

end K8

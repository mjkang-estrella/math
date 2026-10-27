import PotentialMatrix

open scoped BigOperators

namespace WGMParity

theorem terminal_flow_eq_weight {L I : Type*} [Fintype L] [Fintype I] [DecidableEq I]
    (s : L → ℕ) (root : I) (child : I × Bool → L ⊕ I)
    (hc : Function.Injective child) (h : CircuitSound s root child)
    (flow : I → ℝ)
    (hf : (flowMatrix child).mulVec flow =
      fun j => if j = root then ((∑ k, s k : ℕ) : ℝ) else 0) :
    ∀ j, inputFlow child flow (Sum.inl j) = (s j : ℝ) := by
  classical
  have he (u : L → ℝ) :
      dotProduct (fun j => inputFlow child flow (Sum.inl j)) u =
        dotProduct (fun j => (s j : ℝ)) u := by
    obtain ⟨z, hz⟩ := exists_potential_solution child hc u
    have hs := circuitSound_log_equalities s root child h (Sum.elim u z)
      (potential_of_matrix_solution child u z hz)
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    have ha := Matrix.dotProduct_transpose_mulVec (flowMatrix child) flow z
    rw [hz, Matrix.dotProduct_mulVec, hf] at ha
    simp only [dotProduct, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at ha
    simp_rw [terminalMatrix_vecMul] at ha
    change (∑ j, inputFlow child flow (Sum.inl j) * u j) = _
    change _ = (∑ j, (s j : ℝ) * u j)
    rw [ha]
    nlinarith [hs]
  intro j
  have hj := he (Pi.single j 1)
  simpa [dotProduct, Pi.single_apply, mul_ite] using hj

theorem equality_size_forces_even {L I : Type*} [Fintype L] [Fintype I]
    (s : L → ℕ) (hs : ∀ j, 0 < s j) (root : I)
    (child : I × Bool → L ⊕ I) (h : CircuitSound s root child)
    (hsize : Fintype.card I + 1 = Fintype.card L) : Even (∑ j, s j) := by
  classical
  have hl := circuitSound_reaches_leaf s hs root child h
  have hc := equality_count_input_injective root child hl hsize
  have hr := equality_count_root_not_input root child hl hsize
  obtain ⟨flow, hf⟩ := exists_balance_flow child hc root ((∑ j, s j : ℕ) : ℝ)
  have hfm : (flowMatrix child).mulVec flow =
      fun j => if j = root then ((∑ k, s k : ℕ) : ℝ) else 0 := by
    funext j
    rw [flowMatrix_mulVec]
    exact hf j
  have ht := terminal_flow_eq_weight s root child hc h flow hfm
  apply input_balance_forces_even_total child hc root flow (fun j => (s j : ℤ)) (∑ j, s j)
  · intro i b j he
    have hh := ht j
    rw [← he, inputFlow_of_hit child hc flow (i, b)] at hh
    exact_mod_cast hh
  · intro i b j he
    have hj : j ≠ root := by
      intro hj
      apply hr (i, b)
      simpa [hj] using he
    have hh := hf j
    rw [ite_eq_right hj, ← he, inputFlow_of_hit child hc flow (i, b)] at hh
    linarith
  · have hh := hf root
    rw [ite_eq_left rfl, inputFlow_of_miss child flow _ hr] at hh
    linarith

theorem odd_total_sound_size_bound {L I : Type*} [Fintype L] [Fintype I]
    (s : L → ℕ) (hs : ∀ j, 0 < s j) (root : I)
    (child : I × Bool → L ⊕ I) (h : CircuitSound s root child)
    (hodd : Odd (∑ j, s j)) : Fintype.card L ≤ Fintype.card I := by
  classical
  have hl := circuitSound_reaches_leaf s hs root child h
  have hb := reachable_count_bound root child hl
  rw [Nat.card_eq_fintype_card] at hb
  have hi := Fintype.card_subtype_le
    (fun i : I => CircuitReach root child (Sum.inr i))
  by_contra hn
  have heq : Fintype.card I + 1 = Fintype.card L := by omega
  have heven := equality_size_forces_even s hs root child h heq
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  omega

def SourceRepresentation {L I : Type*} [Fintype L]
    (s : L → ℕ) (root : I) (child : I × Bool → L ⊕ I) : Prop :=
  ∀ (x : L → ℝ) (t : ℝ), (∀ j, 0 ≤ x j) → 0 ≤ t →
    (t ^ (∑ j, s j) ≤ ∏ j, x j ^ s j ↔
      ∃ z : I → ℝ, z root = t ∧ (∀ i, 0 ≤ z i) ∧ CircuitFeasible child (Sum.elim x z))

theorem sourceRepresentation_sound {L I : Type*} [Fintype L]
    (s : L → ℕ) (root : I) (child : I × Bool → L ⊕ I)
    (h : SourceRepresentation s root child) : CircuitSound s root child := by
  intro v hv hf
  exact (h (fun j => v (Sum.inl j)) (v (Sum.inr root))
    (fun j => hv (Sum.inl j)) (hv (Sum.inr root))).mpr
      ⟨fun i => v (Sum.inr i), rfl, fun i => hv (Sum.inr i), by
        have he : Sum.elim (fun j => v (Sum.inl j)) (fun i => v (Sum.inr i)) = v := by
          funext w; cases w <;> rfl
        rwa [he]⟩

theorem source_odd_total_bound (m n : ℕ) (s : Fin m → ℕ)
    (hs : ∀ j, 0 < s j) (root : Fin n)
    (child : Fin n × Bool → Fin m ⊕ Fin n)
    (h : SourceRepresentation s root child) (hodd : Odd (∑ j, s j)) : m ≤ n := by
  simpa only [Fintype.card_fin] using odd_total_sound_size_bound s hs root child
    (sourceRepresentation_sound s root child h) hodd

end WGMParity

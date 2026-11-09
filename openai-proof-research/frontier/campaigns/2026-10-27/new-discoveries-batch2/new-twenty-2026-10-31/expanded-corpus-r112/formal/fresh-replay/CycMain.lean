import CycUpper

/-!
# MathDB 374241 / arXiv:2604.16188 Conjecture 4.16

For any `a ≥ 3` and `b ≥ 4`, `R_cyc(S_a, P_b^{mon}) = 1 + (a-1)(b-2)`.
-/

namespace CycRamsey

theorem nonBlue_mod {N : ℕ} (hN : 0 < N) (c : Colouring N) (v : ℕ) :
    nonBlue hN c (v % N) = nonBlue hN c v := by
  unfold nonBlue
  apply Finset.filter_congr
  intro d _
  rw [fm_mod, fm_mod_add]

theorem upper (a b : ℕ) (ha : 3 ≤ a) (hb : 4 ≤ b) :
    CycRamseyProp (startStar a) (monPath b) (1 + (a - 1) * (b - 2)) := by
  classical
  unfold CycRamseyProp
  set N := 1 + (a - 1) * (b - 2) with hNdef
  intro c
  have hN : 0 < N := by omega
  by_cases hstar : ∃ v, v < N ∧ a - 1 ≤ (nonBlue hN c v).card
  · left
    obtain ⟨v, hv, hcard⟩ := hstar
    set O := nonBlue hN c v with hO
    let e := O.orderEmbOfFin rfl
    have hmem : ∀ j, e j ∈ O := fun j => O.orderEmbOfFin_mem rfl j
    have hmem' : ∀ j, 1 ≤ e j ∧ e j < N ∧ c s(fm N hN v, fm N hN (v + e j)) = 0 := by
      intro j
      have h : e j ∈ nonBlue hN c v := hmem j
      simp only [nonBlue, Finset.mem_filter, Finset.mem_Ico] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have ha0 : 0 < a := by omega
    let q : Fin a → ℕ := fun i =>
      if h : i.val = 0 then v else v + e ⟨i.val - 1, by have := i.isLt; omega⟩
    have hq0 : q ⟨0, ha0⟩ = v := by simp [q]
    have hqpos : ∀ (i : Fin a) (h : i.val ≠ 0),
        q i = v + e ⟨i.val - 1, by have := i.isLt; omega⟩ := by
      intro i h; simp [q, h]
    have hq : StrictMono q := by
      intro i j hij
      have hij' : i.val < j.val := hij
      have hj : j.val ≠ 0 := by omega
      rw [hqpos j hj]
      by_cases hi : i.val = 0
      · have : i = ⟨0, ha0⟩ := Fin.ext hi
        rw [this, hq0]
        have := (hmem' ⟨j.val - 1, by have := j.isLt; omega⟩).1
        omega
      · rw [hqpos i hi]
        have : e ⟨i.val - 1, by have := i.isLt; omega⟩ < e ⟨j.val - 1, by have := j.isLt; omega⟩ :=
          e.strictMono (show i.val - 1 < j.val - 1 by omega)
        omega
    have hspan : ∀ i : Fin a, q i < q ⟨0, ha0⟩ + N := by
      intro i
      rw [hq0]
      by_cases hi : i.val = 0
      · have : i = ⟨0, ha0⟩ := Fin.ext hi
        rw [this, hq0]; omega
      · rw [hqpos i hi]
        have := (hmem' ⟨i.val - 1, by have := i.isLt; omega⟩).2.1
        omega
    refine ⟨fun i => (⟨q i % N, Nat.mod_lt _ hN⟩ : Fin N), rot_embedding hN ha0 q hq hspan, ?_⟩
    have hred : ∀ (w : Fin a), w.val ≠ 0 →
        c s((⟨q ⟨0, ha0⟩ % N, Nat.mod_lt _ hN⟩ : Fin N), ⟨q w % N, Nat.mod_lt _ hN⟩) = 0 := by
      intro w hw
      rw [hqpos w hw]
      have := (hmem' ⟨w.val - 1, by have := w.isLt; omega⟩).2.2
      have e0 : (⟨q ⟨0, ha0⟩ % N, Nat.mod_lt _ hN⟩ : Fin N) = fm N hN v := by
        apply Fin.ext; simp [fm, hq0]
      rw [e0]; exact this
    intro u w huw
    rw [startStar, SimpleGraph.fromRel_adj] at huw
    rcases huw.2 with ⟨hu, hw⟩ | ⟨hw, hu⟩
    · have : u = ⟨0, ha0⟩ := Fin.ext hu
      subst this; exact hred w hw
    · have : w = ⟨0, ha0⟩ := Fin.ext hw
      subst this; rw [Sym2.eq_swap]; exact hred u hu
  · right
    push Not at hstar
    have hdeg : ∀ v, (nonBlue hN c v).card ≤ a - 2 := by
      intro v
      rw [← nonBlue_mod hN c v]
      have := hstar (v % N) (Nat.mod_lt _ hN)
      omega
    by_contra hno
    exact theoremA (t := a - 2) (b := b) hN c
      (by rw [hNdef, show a - 2 + 1 = a - 1 by omega]; ring) (by omega) hb hdeg hno

/-- **MathDB 374241** (arXiv:2604.16188, Conjecture 4.16): for all `a ≥ 3`, `b ≥ 4`,
`R_cyc(S_a, P_b^{mon}) = 1 + (a-1)(b-2)`. -/
theorem cycRamsey_startStar_monPath (a b : ℕ) (ha : 3 ≤ a) (hb : 4 ≤ b) :
    cycRamsey (startStar a) (monPath b) = 1 + (a - 1) * (b - 2) := by
  have hleast : IsLeast {n | CycRamseyProp (startStar a) (monPath b) n} (1 + (a - 1) * (b - 2)) := by
    refine ⟨upper a b ha hb, ?_⟩
    intro m hm
    by_contra hlt
    push Not at hlt
    have hm' : m ≤ (a - 1) * (b - 2) := by omega
    rcases hm (blockCol m (a - 1)) with h | h
    · exact no_red_star a m ha h
    · exact no_blue_path a b m ha hb hm' h
  exact hleast.csInf_eq

end CycRamsey

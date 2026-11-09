import CMDRRIncidence

namespace CMDRR
namespace Game
variable {M W : Type}
theorem men_exhaust (g : Game M W) {m n t : M} {w : W}
    (hmn : g.Men m n) (ht : g.Partners t w) : t = m ∨ t = n := by
  classical
  obtain ⟨a,ha,b,hb,hm,hn,hab⟩ := hmn
  have he : ({a,b} : Finset (M × W)) = g.teams := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp [g.two,hab]
  change (t,w) ∈ g.teams at ht
  rw [← he] at ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with ht | ht
  · exact Or.inl ((congrArg Prod.fst ht).trans hm)
  · exact Or.inr ((congrArg Prod.fst ht).trans hn)
end Game

variable {O : Type} [Fintype O]
noncomputable def A (d : Schedule (Fin 5) (Fin 5) O) : ℕ :=
  count (fun o => (d.game o).Women 3 4 ∧
    ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n)
noncomputable def B (d : Schedule (Fin 5) (Fin 5) O) : ℕ :=
  count (fun o => (d.game o).Men 3 4 ∧
    ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v)
noncomputable def z (d : Schedule (Fin 5) (Fin 5) O) : ℕ :=
  count (fun o => (d.game o).Men 3 4 ∧ (d.game o).Women 3 4)

namespace Source
variable {d : Schedule (Fin 5) (Fin 5) O} (h : Source canonical d)
theorem female_single_games_exhaust (x y : Cell canonical) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4) :
    ∀ o, (d.game o).Women 3 4 → ∃ w, (d.game o).Partners x.1.1 w := by
  obtain ⟨a,b,hab,ha,hb,hpa,hpb⟩ := h.row_twoCycle_games x y hxy hx hy
  rw [hx3,hy4] at ha hb
  intro o ho
  rcases count_two_exhaust (fun o => (d.game o).Women 3 4)
    h.canonical_women_repeat hab ha hb o ho with rfl | rfl
  · exact hpa
  · exact hpb

theorem A_zero_of_single_twoCycle (x y : Cell canonical) (hxy : x ≠ y)
    (hx : h.U x = y) (hy : h.U y = x) (hx3 : x.1.2 = 3) (hy4 : y.1.2 = 4)
    (hm : 3 ≤ x.1.1.val) : A d = 0 := by
  classical
  have hn : ∀ o, ¬ ((d.game o).Women 3 4 ∧
      ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n) := by
    rintro o ⟨hw,m,n,hmc,hnc,hmn⟩
    obtain ⟨w,hp⟩ := h.female_single_games_exhaust x y hxy hx hy hx3 hy4 o hw
    rcases (d.game o).men_exhaust hmn hp with he | he
    · rw [he] at hm
      omega
    · rw [he] at hm
      omega
  unfold A count
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro o ho
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ho
  exact hn o ho
end Source
end CMDRR

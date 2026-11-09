import Defs
namespace Cover377831
open scoped BigOperators

theorem no_total_quotient {Q : Type} [Fintype Q]
    (op : Q → Q → Q) (π : Q → Fin 3) (surj : Function.Surjective π)
    (row : ∀ a, Function.Injective (op a))
    (col : ∀ b, Function.Injective (fun a => op a b))
    (support : ∀ a b, (π a, π b, π (op a b)) ∈ H) : False := by
  classical
  have hr (a : Q) (f : Q → ℤ) : (∑ b, f (op a b)) = ∑ b, f b :=
    Fintype.sum_bijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨row a, rfl⟩) _ _ (fun _ => rfl)
  have hc (b : Q) (f : Q → ℤ) : (∑ a, f (op a b)) = ∑ a, f a :=
    Fintype.sum_bijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨col b, rfl⟩) _ _ (fun _ => rfl)
  have hz : (∑ a : Q, ∑ b : Q,
      (Y0 (π b) (π (op a b)) + Y1 (π a) (π (op a b)) + Y2 (π a) (π b))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    exact score_zero _ (support a b)
  have h0 : (∑ a : Q, ∑ b : Q, Y0 (π b) (π (op a b))) =
      ∑ a : Q, ∑ b : Q, Y0 (π a) (π b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    exact hc b (fun c => Y0 (π b) (π c))
  have h1 : (∑ a : Q, ∑ b : Q, Y1 (π a) (π (op a b))) =
      ∑ a : Q, ∑ b : Q, Y1 (π a) (π b) := by
    apply Finset.sum_congr rfl
    intro a _
    exact hr a (fun c => Y1 (π a) (π c))
  have ht : (∑ a : Q, ∑ b : Q, T (π a) (π b)) = 0 := by
    simp only [Finset.sum_add_distrib] at hz
    rw [h0, h1] at hz
    simpa only [T, Finset.sum_add_distrib] using hz
  have hs : (∑ a : Q, ∑ b : Q, (T (π a) (π b) + T (π b) (π a))) = 0 := by
    simp only [Finset.sum_add_distrib]
    have hswap : (∑ a : Q, ∑ b : Q, T (π b) (π a)) = ∑ a : Q, ∑ b : Q, T (π a) (π b) := Finset.sum_comm
    rw [hswap, ht]
    simp
  obtain ⟨a, ha⟩ := surj 0
  obtain ⟨b, hb⟩ := surj 1
  have hn (c d : Q) : T (π c) (π d) + T (π d) (π c) ≤ 0 := by
    rw [symmetric_score]
    split_ifs <;> norm_num
  have hab : (∑ d : Q, (T (π a) (π d) + T (π d) (π a))) < 0 := by
    have hh := Finset.sum_lt_sum (s := (Finset.univ : Finset Q))
      (g := fun _ => (0 : ℤ)) (fun d _ => hn a d)
      (show ∃ d ∈ (Finset.univ : Finset Q), T (π a) (π d) + T (π d) (π a) < 0 from
        ⟨b, Finset.mem_univ _, by rw [symmetric_score, ha, hb]; norm_num⟩)
    simpa using hh
  have hneg : (∑ c : Q, ∑ d : Q, (T (π c) (π d) + T (π d) (π c))) < 0 := by
    have hh := Finset.sum_lt_sum (s := (Finset.univ : Finset Q))
      (g := fun _ => (0 : ℤ)) (fun c _ => Finset.sum_nonpos (fun d _ => hn c d))
      ⟨a, Finset.mem_univ _, hab⟩
    simpa using hh
  omega
end Cover377831

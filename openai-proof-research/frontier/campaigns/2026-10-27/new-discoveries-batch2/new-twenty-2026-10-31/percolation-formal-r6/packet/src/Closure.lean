import Structure
namespace Percolation
set_option autoImplicit false

theorem card_eq_on {α : Type} (xs : List α) (a b : α → Bool)
    (hab : ∀ p, a p = true → b p = true) (he : card xs a = card xs b) :
    ∀ p ∈ xs, a p = b p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hle := card_mono xs a b hab
    have hx := hab x
    simp only [card, List.filter_cons] at he
    cases ha : a x <;> cases hb : b x <;> simp_all [card] <;> omega
theorem step_inflation {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) :
    Subset a (step P r a) := by
  intro p hp
  simp [step, hp]

theorem rounds_inflation {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (n : Nat) :
    Subset a (rounds P r a n) := by
  induction n with
  | zero => exact fun _ h => h
  | succ n ih => exact fun p h => step_inflation P r _ p (ih p h)

theorem card_strict_step {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (hne : step P r a ≠ a) :
    card (List.finRange (size q)) a < card (List.finRange (size q)) (step P r a) := by
  have hle := card_mono (List.finRange (size q)) a (step P r a) (step_inflation P r a)
  have hneq : card (List.finRange (size q)) a ≠ card (List.finRange (size q)) (step P r a) := by
    intro he
    apply hne
    funext p
    exact (card_eq_on _ a (step P r a) (step_inflation P r a) he p (by simp)).symm
  omega

theorem rounds_add {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (n k : Nat) :
    rounds P r a (n+k) = rounds P r (rounds P r a n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change step P r (rounds P r a (n+k)) = step P r (rounds P r (rounds P r a n) k)
    rw [ih]

theorem fixed_later {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (k n : Nat)
    (hkn : k ≤ n) (hf : step P r (rounds P r a k) = rounds P r a k) :
    step P r (rounds P r a n) = rounds P r a n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [rounds_add, rounds_fixed P r _ hf d]
  exact hf

theorem closure_stable {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) :
    step P r (rounds P r a (size q)) = rounds P r a (size q) := by
  by_cases hf : ∃ k, k ≤ size q ∧ step P r (rounds P r a k) = rounds P r a k
  · obtain ⟨k, hk, hf⟩ := hf
    exact fixed_later P r a k (size q) hk hf
  · have hg : ∀ n, n ≤ size q + 1 → n ≤ card (List.finRange (size q)) (rounds P r a n) := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        have hi := ih (by omega)
        have hne : step P r (rounds P r a n) ≠ rounds P r a n :=
          fun he => hf ⟨n, by omega, he⟩
        have hs := card_strict_step P r (rounds P r a n) hne
        change n+1 ≤ card (List.finRange (size q)) (step P r (rounds P r a n))
        omega
    have hlo := hg (size q + 1) (by omega)
    have hhi := List.length_filter_le (fun p => rounds P r a (size q + 1) p) (List.finRange (size q))
    simp only [List.length_finRange] at hhi
    change card (List.finRange (size q)) (rounds P r a (size q + 1)) ≤ size q at hhi
    unfold card at hlo hhi
    omega

theorem minimal_deletion_separator {q : Nat} (P : Plane q) (r : Nat)
    (a : Infection q) (hm : Minimal P r a) (v : Points q) (hv : a v = true) :
    let b := rounds P r (erase a v) (size q)
    (∀ p, p ≠ v → a p = true → b p = true) ∧ step P r b = b ∧ b v = false := by
  dsimp only
  have hfix := closure_stable P r (erase a v)
  refine ⟨?_, hfix, ?_⟩
  · intro p hp ha
    exact rounds_inflation P r (erase a v) (size q) p (by simp [erase, ha, hp])
  · cases hb : rounds P r (erase a v) (size q) v with
    | false => rfl
    | true =>
      have hsub : Subset a (rounds P r (erase a v) (size q)) := by
        intro p hp
        by_cases he : p = v
        · subst p; exact hb
        · exact rounds_inflation P r (erase a v) (size q) p (by simp [erase, hp, he])
      have hnon := hm.2 (erase a v) (fun p hp => by simp only [erase, Bool.and_eq_true] at hp; exact hp.1) (by
        intro he
        have hh := congrFun he v
        simp [erase, hv] at hh)
      obtain ⟨n, hn⟩ := hm.1
      have hall : Full (rounds P r (erase a v) (size q)) := by
        intro p
        have ht := rounds_mono P r hsub n p (hn p)
        rw [rounds_fixed P r _ hfix n] at ht
        exact ht
      exact False.elim (hnon ⟨size q, hall⟩)
end Percolation

import ListCertificate
import Existence
set_option autoImplicit false
namespace Polyomino57

def arrayClosureCheck (A B : Array (List GridPoint))
    (choices : List GridPoint → GridPoint → ℕ × GridPoint) : Bool :=
  A.toList.all (fun row => successorRowCheck B row (choices row))

def arrayTerminalCheck (A : Array (List GridPoint))
    (shifts : List GridPoint → GridPoint) : Bool :=
  A.toList.all (fun row => numericPlacement row (shifts row))

theorem certificate_growth_coverage (L : ℕ → Array (List GridPoint)) (n : ℕ)
    (choices : ℕ → List GridPoint → GridPoint → ℕ × GridPoint)
    (base : [(0,0)] ∈ (L 0).toList)
    (steps : ∀ k < n, arrayClosureCheck (L k) (L (k+1)) (choices k) = true)
    {P : Finset GridPoint} (hg : Grown P) (hc : P.card-1 ≤ n) :
    ∃ row ∈ (L (P.card-1)).toList, ∃ hr : row.toFinset.Nonempty,
      normalize P (growth_sound hg).1 = normalize row.toFinset hr := by
  induction hg with
  | singleton p =>
    refine ⟨[(0,0)],base,by simp,?_⟩
    simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using
      (normalize_singleton p).trans (normalize_singleton (0,0)).symm
  | @insert Q a b hg ha hb hab ih =>
    have hpos : 1 ≤ Q.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hcard := Finset.card_insert_of_notMem hb
    have hlt : Q.card-1 < n := by omega
    obtain ⟨row,hr,hrne,he⟩ := ih (by omega)
    have checked := List.all_eq_true.mp (steps (Q.card-1) hlt) row hr
    obtain ⟨S,hS,hSne,hEq⟩ := represented_growth_step (L ((Q.card-1)+1))
      Q row.toFinset (growth_sound hg).1 hrne he row rfl (choices (Q.card-1) row)
      checked ha hb hab
    have hindex : (insert b Q).card-1 = (Q.card-1)+1 := by omega
    rw [hindex]
    exact ⟨S,hS,hSne,hEq⟩

-- CONDITIONAL interface. Both finite closure and terminal checks must be supplied.
theorem universal_of_array_certificates (L : ℕ → Array (List GridPoint))
    (choices : ℕ → List GridPoint → GridPoint → ℕ × GridPoint)
    (shifts : List GridPoint → GridPoint)
    (base : [(0,0)] ∈ (L 0).toList)
    (steps : ∀ k < 10, arrayClosureCheck (L k) (L (k+1)) (choices k) = true)
    (terminal : arrayTerminalCheck (L 10) shifts = true) : UniversalContainer 11 witness := by
  refine ⟨witness_connected,?_⟩
  intro P hP hc
  obtain ⟨row,hr,hrne,he⟩ := certificate_growth_coverage L 10 choices base steps
    (growth_complete hP) (by omega)
  rw [hc] at hr
  obtain ⟨t,ht⟩ := equal_normalizations_are_translates P row.toFinset hP.1 hrne he
  have hcheck := List.all_eq_true.mp terminal row hr
  have hsub := (numericPlacement_iff row (shifts row)).mp hcheck
  refine ⟨(t.1+(shifts row).1,t.2+(shifts row).2),?_⟩
  rw [← translate_comp,ht]
  exact hsub

-- This conclusion is also CONDITIONAL on the same still-unchecked certificate data.
theorem refutation_of_array_certificates (L : ℕ → Array (List GridPoint))
    (choices : ℕ → List GridPoint → GridPoint → ℕ × GridPoint)
    (shifts : List GridPoint → GridPoint)
    (base : [(0,0)] ∈ (L 0).toList)
    (steps : ∀ k < 10, arrayClosureCheck (L k) (L (k+1)) (choices k) = true)
    (terminal : arrayTerminalCheck (L 10) shifts = true) : ¬ SourceFormula :=
  refute_of_container witness witness_card
    (universal_of_array_certificates L choices shifts base steps terminal)
end Polyomino57

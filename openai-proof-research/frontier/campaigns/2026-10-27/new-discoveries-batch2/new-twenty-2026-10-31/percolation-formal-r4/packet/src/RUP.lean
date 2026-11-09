import TruthTableCNF
namespace Percolation.CNF
set_option autoImplicit false
abbrev Lit := Nat × Bool
abbrev NClause := Clause Nat

def remaining (f c : NClause) : NClause := c.filter (fun z => !f.contains z)
noncomputable def rup (f : NClause) (hs : List NClause) : Bool :=
  List.rec (motive := fun _ => NClause → Bool) (fun _ => false)
    (fun c _ prev fs => match remaining fs c with
      | [] => true
      | [z] => prev ((z.1, !z.2) :: fs)
      | _ => false) hs f

theorem remaining_sound (v : Nat → Bool) (f c : NClause)
    (hf : ∀ z ∈ f, v z.1 = z.2) (hc : Holds v c) : Holds v (remaining f c) := by
  obtain ⟨z, hz, hv⟩ := hc
  refine ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, hv⟩
  simp only [Bool.not_eq_true', Bool.eq_false_iff]
  intro h
  exact hv (hf z (List.mem_of_elem_eq_true h))

theorem rup_sound_aux (v : Nat → Bool) (hs : List NClause) :
    ∀ f, (∀ z ∈ f, v z.1 = z.2) →
    (∀ c ∈ hs, Holds v c) → rup f hs = true → False := by
  induction hs with
  | nil => intro f hf hh he; simp [rup] at he
  | cons c cs ih =>
    intro f hf hh he
    have hc := remaining_sound v f c hf (hh c (by simp))
    cases hr : remaining f c with
    | nil => simp [Holds, hr] at hc
    | cons z zs =>
      cases zs with
      | nil =>
        have hv : v z.1 ≠ z.2 := by simpa [Holds, hr] using hc
        have hn : v z.1 = !z.2 := by cases h : v z.1 <;> cases hb : z.2 <;> simp_all
        apply ih ((z.1, !z.2) :: f)
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hn
          · exact hf w hw
        · intro d hd; exact hh d (by simp [hd])
        · simpa [rup, hr] using he
      | cons w ws => simp [rup, hr] at he

theorem rup_sound (c : NClause) (hs : List NClause) (he : rup c hs = true)
    (v : Nat → Bool) (hh : ∀ d ∈ hs, Holds v d) : Holds v c := by
  apply Classical.byContradiction
  intro hn
  apply rup_sound_aux v hs c _ hh he
  intro z hz
  apply Classical.byContradiction
  intro h
  exact hn ⟨z, hz, h⟩
#print axioms rup_sound
end Percolation.CNF

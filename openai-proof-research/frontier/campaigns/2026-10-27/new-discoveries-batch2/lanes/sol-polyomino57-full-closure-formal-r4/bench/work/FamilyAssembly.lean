import LocalAssembly
set_option autoImplicit false
namespace Polyomino57
-- The finite array is row-local; membership in the target family is proved
-- separately. Thus evaluating a row never evaluates a global target array.
def FamilyRowClosed (B : List GridPoint → Prop) (row : List GridPoint) : Prop :=
  ∃ next : Array (List GridPoint), ∃ choice : GridPoint → ℕ × GridPoint,
    (∀ S ∈ next.toList, B S) ∧ successorFastRowCheck next row choice = true

theorem family_growth_step (B : List GridPoint → Prop) (P : Finset GridPoint)
    (hP : P.Nonempty) (row : List GridPoint) (hr : row.toFinset.Nonempty)
    (he : normalize P hP = normalize row.toFinset hr)
    (checked : FamilyRowClosed B row)
    {a b : GridPoint} (ha : a ∈ P) (hb : b ∉ P) (hab : Adj a b) :
    ∃ S, B S ∧ ∃ hS : S.toFinset.Nonempty,
      normalize (insert b P) (Finset.insert_nonempty _ _) = normalize S.toFinset hS := by
  obtain ⟨next,choice,hm,hc⟩ := checked
  obtain ⟨S,hS,hSne,hEq⟩ := represented_growth_step next P row.toFinset
    hP hr he row rfl choice (successorFastRowCheck_implies next row choice hc) ha hb hab
  exact ⟨S,hm S hS,hSne,hEq⟩

theorem family_growth_coverage (F : ℕ → List GridPoint → Prop) (n : ℕ)
    (base : F 0 [(0,0)])
    (steps : ∀ k < n, ∀ row, F k row → FamilyRowClosed (F (k+1)) row)
    {P : Finset GridPoint} (hg : Grown P) (hc : P.card-1 ≤ n) :
    ∃ row, F (P.card-1) row ∧ ∃ hr : row.toFinset.Nonempty,
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
    obtain ⟨S,hS,hSne,hEq⟩ := family_growth_step (F ((Q.card-1)+1))
      Q (growth_sound hg).1 row hrne he (steps (Q.card-1) hlt row hr) ha hb hab
    have hindex : (insert b Q).card-1 = (Q.card-1)+1 := by omega
    rw [hindex]
    exact ⟨S,hS,hSne,hEq⟩

-- Terminal family may be defined directly by actual TreeMember occurrences;
-- the supplied terminal theorem must still prove every member's placement.
theorem universal_of_family_certificates (F : ℕ → List GridPoint → Prop)
    (base : F 0 [(0,0)])
    (steps : ∀ k < 10, ∀ row, F k row → FamilyRowClosed (F (k+1)) row)
    (terminal : ∀ row, F 10 row → ∃ t, translate t row.toFinset ⊆ witness) :
    UniversalContainer 11 witness := by
  refine ⟨witness_connected,?_⟩
  intro P hP hc
  obtain ⟨row,hr,hrne,he⟩ := family_growth_coverage F 10 base steps
    (growth_complete hP) (by omega)
  rw [hc] at hr
  obtain ⟨t,ht⟩ := terminal row hr
  exact placement_of_normalized_row P hP.1 (row,t) hrne he ht
end Polyomino57

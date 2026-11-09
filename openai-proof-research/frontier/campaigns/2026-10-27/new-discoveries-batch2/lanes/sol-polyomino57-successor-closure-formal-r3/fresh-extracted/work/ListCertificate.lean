import Efficient
import Coverage
set_option autoImplicit false
namespace Polyomino57
-- Executable point-list equality up to a supplied translation.
-- Certificate lookup can use an array index rather than a linear shape search.
def shiftedCells (P : List GridPoint) (t : GridPoint) : List GridPoint :=
  P.map (fun p => (p.1+t.1,p.2+t.2))
def cellsEqCheck (P Q : List GridPoint) : Bool :=
  P.all (fun p => Q.contains p) && Q.all (fun q => P.contains q)

theorem cellsEqCheck_iff (P Q : List GridPoint) :
    cellsEqCheck P Q = true ↔ P.toFinset = Q.toFinset := by
  simp only [cellsEqCheck, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · intro p hp
      exact List.mem_toFinset.mpr (h.1 p (List.mem_toFinset.mp hp))
    · intro p hp
      exact List.mem_toFinset.mpr (h.2 p (List.mem_toFinset.mp hp))
  · intro h
    constructor
    · intro p hp
      exact List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hp)
    · intro p hp
      exact List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hp)

theorem shiftedCells_semantics (P : List GridPoint) (t : GridPoint) :
    (shiftedCells P t).toFinset = translate t P.toFinset := by
  ext q
  simp [shiftedCells, translate]

def translationEqCheck (P Q : List GridPoint) (t : GridPoint) : Bool :=
  cellsEqCheck (shiftedCells P t) Q

theorem translationEqCheck_sound (P Q : List GridPoint) (t : GridPoint)
    (h : translationEqCheck P Q t = true) : translate t P.toFinset = Q.toFinset := by
  exact (shiftedCells_semantics P t) ▸ (cellsEqCheck_iff _ _).mp h

-- A local edge certificate supplies a target array index and an integer shift.
def edgeCheck (next : Array (List GridPoint)) (P : List GridPoint)
    (b : GridPoint) (index : ℕ) (t : GridPoint) : Bool :=
  if hi : index < next.size then translationEqCheck (b :: P) next[index] t else false

theorem edgeCheck_sound (next : Array (List GridPoint)) (P : List GridPoint)
    (b : GridPoint) (index : ℕ) (t : GridPoint)
    (h : edgeCheck next P b index t = true) :
    ∃ Q ∈ next.toList, ∃ hQ : Q.toFinset.Nonempty,
      normalize (insert b P.toFinset) (Finset.insert_nonempty _ _) = normalize Q.toFinset hQ := by
  unfold edgeCheck at h
  split at h
  next hi =>
    have he := translationEqCheck_sound (b :: P) next[index] t h
    have he' : translate t (insert b P.toFinset) = next[index].toFinset := by
      simpa only [List.toFinset_cons] using he
    have hne : next[index].toFinset.Nonempty := he' ▸ translate_nonempty _ (Finset.insert_nonempty _ _) t
    refine ⟨next[index],?_,hne,?_⟩
    · exact List.mem_iff_get.mpr ⟨⟨index,by simpa using hi⟩,by simp⟩
    · exact (normalize_iff_translate _ _ (Finset.insert_nonempty _ _) hne).mpr ⟨t,he'⟩
  next => simp at h
end Polyomino57

namespace Polyomino57
def neighborCells (a : GridPoint) : List GridPoint :=
  [(a.1+1,a.2),(a.1-1,a.2),(a.1,a.2+1),(a.1,a.2-1)]
theorem mem_neighborCells (a b : GridPoint) : b ∈ neighborCells a ↔ Adj a b := by
  simp [neighborCells,Adj,Prod.ext_iff]

def successorRowCheck (next : Array (List GridPoint)) (P : List GridPoint)
    (choice : GridPoint → ℕ × GridPoint) : Bool :=
  P.all (fun a => (neighborCells a).all (fun b =>
    P.contains b || edgeCheck next P b (choice b).1 (choice b).2))

theorem successorRowCheck_sound (next : Array (List GridPoint)) (P : List GridPoint)
    (choice : GridPoint → ℕ × GridPoint) (h : successorRowCheck next P choice = true)
    {a b : GridPoint} (ha : a ∈ P.toFinset) (hb : b ∉ P.toFinset) (hab : Adj a b) :
    ∃ Q ∈ next.toList, ∃ hQ : Q.toFinset.Nonempty,
      normalize (insert b P.toFinset) (Finset.insert_nonempty _ _) = normalize Q.toFinset hQ := by
  have he := List.all_eq_true.mp (List.all_eq_true.mp h a (List.mem_toFinset.mp ha))
    b ((mem_neighborCells a b).mpr hab)
  have hn : P.contains b = false := by simp [List.mem_toFinset] at *; exact hb
  rw [hn, Bool.false_or] at he
  exact edgeCheck_sound next P b _ _ he

-- The only hypotheses here are local executable certificate results.
-- No terminal-family count or external equality is used.
theorem represented_growth_step (next : Array (List GridPoint)) (P Q : Finset GridPoint)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (eqnorm : normalize P hP = normalize Q hQ)
    (row : List GridPoint) (hrow : row.toFinset = Q)
    (choice : GridPoint → ℕ × GridPoint)
    (checked : successorRowCheck next row choice = true)
    {a b : GridPoint} (ha : a ∈ P) (hb : b ∉ P) (hab : Adj a b) :
    ∃ S ∈ next.toList, ∃ hS : S.toFinset.Nonempty,
      normalize (insert b P) (Finset.insert_nonempty _ _) = normalize S.toFinset hS := by
  obtain ⟨t,ht⟩ := equal_normalizations_are_translates P Q hP hQ eqnorm
  have hat : (a.1+t.1,a.2+t.2) ∈ row.toFinset := by
    rw [hrow,← ht]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hbt : (b.1+t.1,b.2+t.2) ∉ row.toFinset := by
    rw [hrow,← ht]
    intro hm
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hm
    have he' : c = b := by
      have hh := Prod.mk.inj he
      apply Prod.ext <;> omega
    exact hb (he' ▸ hc)
  obtain ⟨S,hS,hne,he⟩ := successorRowCheck_sound next row choice checked hat hbt
    ((adj_translate t a b).mpr hab)
  refine ⟨S,hS,hne,?_⟩
  have hs : normalize (insert b P) (Finset.insert_nonempty _ _) =
      normalize (insert (b.1+t.1,b.2+t.2) row.toFinset) (Finset.insert_nonempty _ _) := by
    apply (normalize_iff_translate _ _ _ _).mpr
    exact ⟨t,by rw [translate_insert, ht, hrow]⟩
  exact hs.trans he
end Polyomino57

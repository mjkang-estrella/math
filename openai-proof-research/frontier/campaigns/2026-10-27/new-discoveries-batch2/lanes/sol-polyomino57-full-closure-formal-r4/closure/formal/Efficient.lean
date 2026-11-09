import Witness
set_option autoImplicit false
namespace Polyomino57
-- No Finset construction or membership occurs during numeric checking.
def inDiamond (p : GridPoint) : Bool :=
  decide (p.1.natAbs + p.2.natAbs ≤ 5) &&
    !(decide (p.1.natAbs = 2) && decide (p.2.natAbs = 2))

theorem mem_square (p : GridPoint) : p ∈ square ↔
    -5 ≤ p.1 ∧ p.1 ≤ 5 ∧ -5 ≤ p.2 ∧ p.2 ≤ 5 := by
  simp only [square, List.bind_eq_flatMap, List.pure_def, List.mem_toFinset,
    List.mem_flatMap, List.mem_map, List.mem_singleton, List.mem_range]
  constructor
  · rintro ⟨x,⟨a,ha,hax⟩,y,⟨b,hb,hby⟩,he⟩
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp at he1 he2
    omega
  · intro h
    refine ⟨p.1+5,⟨(p.1+5).toNat,by omega,by omega⟩,
      p.2+5,⟨(p.2+5).toNat,by omega,by omega⟩,?_⟩
    ext <;> dsimp <;> omega

theorem inDiamond_iff (p : GridPoint) : inDiamond p = true ↔ p ∈ witness := by
  rw [witness_literal]
  unfold diamondMinusFour
  simp only [inDiamond, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Finset.mem_filter]
  rw [mem_square]
  constructor
  · intro h
    have hx : p.1.natAbs ≤ 5 := by omega
    have hy : p.2.natAbs ≤ 5 := by omega
    exact ⟨by omega, h.1, by tauto⟩
  · intro h
    exact ⟨h.2.1, by tauto⟩

def numericPlacement (P : List GridPoint) (t : GridPoint) : Bool :=
  P.all (fun p => inDiamond (p.1+t.1,p.2+t.2))

theorem numericPlacement_iff (P : List GridPoint) (t : GridPoint) :
    numericPlacement P t = true ↔ translate t P.toFinset ⊆ witness := by
  simp only [numericPlacement, List.all_eq_true]
  constructor
  · intro h q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (inDiamond_iff _).mp (h p (List.mem_toFinset.mp hp))
  · intro h p hp
    exact (inDiamond_iff _).mpr (h (Finset.mem_image.mpr
      ⟨p,List.mem_toFinset.mpr hp,rfl⟩))

def numericBatch (rows : List (List GridPoint × GridPoint)) : Bool :=
  rows.all (fun row => numericPlacement row.1 row.2)

theorem numericBatch_sound (rows : List (List GridPoint × GridPoint))
    (h : numericBatch rows = true) :
    ∀ row ∈ rows, translate row.2 row.1.toFinset ⊆ witness := by
  intro row hr
  exact (numericPlacement_iff _ _).mp (List.all_eq_true.mp h row hr)
end Polyomino57

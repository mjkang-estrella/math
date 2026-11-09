import ChordComb2Base
namespace Chord.Comb2
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

def dihedral4 (r : Nat) (rev : Bool) : Fin 8 ≃ Fin 8 where
  toFun i := ⟨(if rev then r+8-1-i.val else i.val+r)%8, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨(if rev then r+8-1-i.val else i.val+8-r%8)%8, Nat.mod_lt _ (by decide)⟩
  left_inv := by intro i; apply Fin.ext; simp only; split <;> omega
  right_inv := by intro i; apply Fin.ext; simp only; split <;> omega

def Orbit4 (D E : Diagram 4) : Prop := ∃ r : Fin 8, ∃ v : Bool,
  ∀ i, E.partner (dihedral4 r.val v i) = dihedral4 r.val v (D.partner i)
instance (D E : Diagram 4) : Decidable (Orbit4 D E) := by unfold Orbit4; infer_instance

theorem orbit4_generator {D E : Diagram 4} (h : Orbit4 D E) : Generator D E := by
  obtain ⟨r,v,h⟩ := h
  refine ⟨dihedral4 r.val v, ?_, h⟩
  cases v
  · exact Or.inl ⟨r.val, fun _ => rfl⟩
  · exact Or.inr ⟨r.val, fun _ => rfl⟩

theorem generator_orbit4 {D E : Diagram 4} (h : Generator D E) : Orbit4 D E := by
  obtain ⟨e, (⟨r,hr⟩ | ⟨r,hr⟩), he⟩ := h
  · have hh : ∀ i, e i = dihedral4 (r%8) false i := by
      intro i
      apply Fin.ext
      have := hr i
      simp only [dihedral4, Bool.false_eq_true, ↓reduceIte, Equiv.coe_fn_mk]
      omega
    refine ⟨⟨r%8, Nat.mod_lt _ (by decide)⟩, false, ?_⟩
    simpa only [hh] using he
  · have hh : ∀ i, e i = dihedral4 (r%8) true i := by
      intro i
      apply Fin.ext
      have := hr i
      have hi := i.isLt
      simp only [dihedral4, ↓reduceIte, Equiv.coe_fn_mk]
      omega
    refine ⟨⟨r%8, Nat.mod_lt _ (by decide)⟩, true, ?_⟩
    simpa only [hh] using he

theorem orbit4_refl (D : Diagram 4) : Orbit4 D D := by
  refine ⟨0,false,?_⟩
  intro i
  have h : ∀ i : Fin 8, dihedral4 0 false i = i := by decide
  change D.partner (dihedral4 0 false i) = dihedral4 0 false (D.partner i)
  rw [h, h]

theorem orbit4_trans {D E F : Diagram 4} (h : Orbit4 D E) (k : Orbit4 E F) : Orbit4 D F := by
  obtain ⟨r,v,hr⟩ := h
  obtain ⟨s,w,hs⟩ := k
  let t : Fin 8 := ⟨(if w then s.val+8-r.val else s.val+r.val)%8, Nat.mod_lt _ (by decide)⟩
  let z := Bool.xor v w
  have comp : ∀ r s : Fin 8, ∀ v w : Bool, ∀ i,
      dihedral4 ((if w then s.val+8-r.val else s.val+r.val)%8) (Bool.xor v w) i =
      dihedral4 s.val w (dihedral4 r.val v i) := by decide
  have ht := comp r s v w
  refine ⟨t,z,?_⟩
  intro i
  rw [ht, hs, hr, ht]

theorem orbit4_symm {D E : Diagram 4} (h : Orbit4 D E) : Orbit4 E D := by
  obtain ⟨r,v,hr⟩ := h
  let s : Fin 8 := ⟨(if v then r.val else 8-r.val)%8, Nat.mod_lt _ (by decide)⟩
  let w := v
  have inv : ∀ r : Fin 8, ∀ v : Bool, ∀ i,
      dihedral4 ((if v then r.val else 8-r.val)%8) v i =
      (dihedral4 r.val v).symm i := by decide
  have hs := inv r v
  refine ⟨s,w,?_⟩
  intro i
  change D.partner (dihedral4 ((if v then r.val else 8-r.val)%8) v i) =
    dihedral4 ((if v then r.val else 8-r.val)%8) v (E.partner i)
  apply (dihedral4 r.val v).injective
  simp only [hs, Equiv.apply_symm_apply]
  rw [←hr]
  simp only [Equiv.apply_symm_apply]

theorem equivalent_orbit4 {D E : Diagram 4} (h : Equivalent D E) : Orbit4 D E := by
  induction h with
  | rel _ _ h => exact generator_orbit4 h
  | refl D => exact orbit4_refl D
  | symm _ _ _ ih => exact orbit4_symm ih
  | trans _ _ _ _ _ ih ik => exact orbit4_trans ih ik

def fourReps (i : Fin 4) : Diagram 4 := if i=0 then exception0 else if i=1 then exception1 else if i=2 then exception2 else exception3

theorem fourReps_range (i : Fin 4) : Range12 (fourReps i) := by
  fin_cases i
  · exact exception0_range
  · exact exception1_range
  · exact exception2_range
  · exact exception3_range

theorem fourReps_distinct (i j : Fin 4) (h : Equivalent (fourReps i) (fourReps j)) : i=j := by
  have h' := equivalent_orbit4 h
  clear h
  fin_cases i <;> fin_cases j <;> revert h' <;> decide
end Chord.Comb2

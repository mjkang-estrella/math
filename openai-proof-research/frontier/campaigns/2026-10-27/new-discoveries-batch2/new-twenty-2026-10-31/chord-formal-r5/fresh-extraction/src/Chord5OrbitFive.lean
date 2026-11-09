import ChordComb2OrbitFour
namespace Chord.Round5
open Comb2
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
def Orbit5 (D E : Diagram 5) : Prop := ∃ r : Fin 10, ∃ v : Bool,
  ∀ i, E.partner (dihedral5 r.val v i) = dihedral5 r.val v (D.partner i)
instance (D E : Diagram 5) : Decidable (Orbit5 D E) := by unfold Orbit5; infer_instance

theorem orbit5_generator {D E : Diagram 5} (h : Orbit5 D E) : Generator D E := by
  obtain ⟨r,v,h⟩ := h
  refine ⟨dihedral5 r.val v, ?_, h⟩
  cases v
  · exact Or.inl ⟨r.val, fun _ => rfl⟩
  · exact Or.inr ⟨r.val, fun _ => rfl⟩

theorem generator_orbit5 {D E : Diagram 5} (h : Generator D E) : Orbit5 D E := by
  obtain ⟨e, (⟨r,hr⟩ | ⟨r,hr⟩), he⟩ := h
  · have hh : ∀ i, e i = dihedral5 (r%10) false i := by
      intro i
      apply Fin.ext
      have := hr i
      simp only [dihedral5, Bool.false_eq_true, ↓reduceIte, Equiv.coe_fn_mk]
      omega
    refine ⟨⟨r%10, Nat.mod_lt _ (by decide)⟩, false, ?_⟩
    simpa only [hh] using he
  · have hh : ∀ i, e i = dihedral5 (r%10) true i := by
      intro i
      apply Fin.ext
      have := hr i
      have hi := i.isLt
      simp only [dihedral5, ↓reduceIte, Equiv.coe_fn_mk]
      omega
    refine ⟨⟨r%10, Nat.mod_lt _ (by decide)⟩, true, ?_⟩
    simpa only [hh] using he

theorem orbit5_refl (D : Diagram 5) : Orbit5 D D := by
  refine ⟨0,false,?_⟩
  intro i
  have h : ∀ i : Fin 10, dihedral5 0 false i = i := by decide
  change D.partner (dihedral5 0 false i) = dihedral5 0 false (D.partner i)
  rw [h, h]

theorem orbit5_trans {D E F : Diagram 5} (h : Orbit5 D E) (k : Orbit5 E F) : Orbit5 D F := by
  obtain ⟨r,v,hr⟩ := h
  obtain ⟨s,w,hs⟩ := k
  let t : Fin 10 := ⟨(if w then s.val+10-r.val else s.val+r.val)%10, Nat.mod_lt _ (by decide)⟩
  let z := Bool.xor v w
  have comp : ∀ r s : Fin 10, ∀ v w : Bool, ∀ i,
      dihedral5 ((if w then s.val+10-r.val else s.val+r.val)%10) (Bool.xor v w) i =
      dihedral5 s.val w (dihedral5 r.val v i) := by decide
  have ht := comp r s v w
  refine ⟨t,z,?_⟩
  intro i
  rw [ht, hs, hr, ht]

theorem orbit5_symm {D E : Diagram 5} (h : Orbit5 D E) : Orbit5 E D := by
  obtain ⟨r,v,hr⟩ := h
  let s : Fin 10 := ⟨(if v then r.val else 10-r.val)%10, Nat.mod_lt _ (by decide)⟩
  let w := v
  have inv : ∀ r : Fin 10, ∀ v : Bool, ∀ i,
      dihedral5 ((if v then r.val else 10-r.val)%10) v i =
      (dihedral5 r.val v).symm i := by decide
  have hs := inv r v
  refine ⟨s,w,?_⟩
  intro i
  change D.partner (dihedral5 ((if v then r.val else 10-r.val)%10) v i) =
    dihedral5 ((if v then r.val else 10-r.val)%10) v (E.partner i)
  apply (dihedral5 r.val v).injective
  simp only [hs, Equiv.apply_symm_apply]
  rw [←hr]
  simp only [Equiv.apply_symm_apply]

theorem equivalent_orbit5 {D E : Diagram 5} (h : Equivalent D E) : Orbit5 D E := by
  induction h with
  | rel _ _ h => exact generator_orbit5 h
  | refl D => exact orbit5_refl D
  | symm _ _ _ ih => exact orbit5_symm ih
  | trans _ _ _ _ _ ih ik => exact orbit5_trans ih ik

def conjugateFive (r : Fin 10) (rev : Bool) : Diagram 5 where
  partner i := (dihedral5 r.val rev).symm ((r3Block 5 (by decide)).partner (dihedral5 r.val rev i))
  involutive i := by simp only [Equiv.apply_symm_apply, Diagram.involutive, Equiv.symm_apply_apply]
  noFixed i h := by
    have hh := congrArg (dihedral5 r.val rev) h
    simp only [Equiv.apply_symm_apply] at hh
    exact (r3Block 5 (by decide)).noFixed _ hh

theorem equivalent_conjugateFive (D : Diagram 5)
    (h : Equivalent D (r3Block 5 (by decide))) :
    ∃ r rev, D = conjugateFive r rev := by
  obtain ⟨r,rev,hr⟩ := equivalent_orbit5 h
  refine ⟨r,rev,?_⟩
  apply diagram_ext
  funext i
  apply (dihedral5 r.val rev).injective
  simpa only [conjugateFive, Equiv.apply_symm_apply] using (hr i).symm

def triangleDarts (D : Diagram 5) (a b c : Fin 10) : Finset (Fin 10) :=
  {a,D.partner a,b,D.partner b,c,D.partner c}

/-- A chosen triangle always maps to the same six core endpoints. -/
private theorem triangle_core_check : ∀ r : Fin 10, ∀ rev : Bool, ∀ a b c : Fin 10,
    Crosses (conjugateFive r rev) a b → Crosses (conjugateFive r rev) a c →
    Crosses (conjugateFive r rev) b c →
    triangleDarts (conjugateFive r rev) a b c =
      Finset.univ.filter (fun i => (dihedral5 r.val rev i).val < 6) := by decide

/-- Uniqueness of the triangle's endpoint set under the frozen equivalence closure. -/
theorem triangle_endpoints_unique (D : Diagram 5)
    (h : Equivalent D (r3Block 5 (by decide)))
    (a b c x y z : Fin 10)
    (hab : Crosses D a b) (hac : Crosses D a c) (hbc : Crosses D b c)
    (hxy : Crosses D x y) (hxz : Crosses D x z) (hyz : Crosses D y z) :
    triangleDarts D a b c = triangleDarts D x y z := by
  obtain ⟨r,rev,rfl⟩ := equivalent_conjugateFive D h
  exact (triangle_core_check r rev a b c hab hac hbc).trans
    (triangle_core_check r rev x y z hxy hxz hyz).symm

#print axioms triangle_endpoints_unique
end Chord.Round5

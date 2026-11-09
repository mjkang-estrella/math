import CodeLoopRepresentations

abbrev SourceSign := {z : Int // z = 1 ∨ z = -1}

def signValue (a : ZMod 2) : Int := if a = 0 then 1 else -1

def signEquiv : ZMod 2 ≃ SourceSign where
  toFun a := ⟨signValue a, by unfold signValue; split <;> simp⟩
  invFun a := if a.val = 1 then 0 else 1
  left_inv a := by
    rcases zmod2_cases a with h | h <;> subst a <;> decide
  right_inv a := by
    apply Subtype.ext
    rcases a.property with h | h <;> simp [signValue,h]

theorem signValue_zero : signValue 0 = 1 := by decide

theorem signValue_add (a b : ZMod 2) : signValue (a+b) = signValue a * signValue b := by
  rcases zmod2_cases a with h | h <;> subst a <;>
  rcases zmod2_cases b with h | h <;> subst b <;> decide

theorem signValue_natCast (n : Nat) : signValue (n : ZMod 2) = (-1 : Int)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.cast_succ,signValue_add,ih,pow_succ]
    rfl

noncomputable def sourcePhi (i : Fin 2) (v w : D i) : SourceSign :=
  signEquiv (codeFactor i v w)

theorem sourcePhi_diagonal (i : Fin 2) (v : D i) :
    (sourcePhi i v v).val = (-1 : Int)^(wordWeight v.val / 4) := by
  change signValue (codeFactor i v v) = _
  rw [codeFactor_diagonal,signValue_natCast]

theorem sourcePhi_symmetry (i : Fin 2) (v w : D i) :
    (sourcePhi i v w).val = (-1 : Int)^(pairWeight v.val w.val / 2) * (sourcePhi i w v).val := by
  have he := congrArg signValue (codeFactor_symmetry i v w)
  rw [signValue_add,signValue_natCast] at he
  have hs := (sourcePhi i w v).property
  change signValue (codeFactor i w v) = 1 ∨ signValue (codeFactor i w v) = -1 at hs
  change signValue (codeFactor i v w) = _ * signValue (codeFactor i w v)
  rcases hs with hs | hs <;> rw [hs] at he ⊢ <;> omega

theorem sourcePhi_normalization (i : Fin 2) (v : D i) :
    (sourcePhi i 0 v).val = 1 ∧ (sourcePhi i v 0).val = 1 := by
  change signValue (codeFactor i 0 v) = 1 ∧ signValue (codeFactor i v 0) = 1
  rw [codeFactor_zero_left,codeFactor_zero_right,signValue_zero]
  exact ⟨rfl,rfl⟩


theorem signValue_square (a : ZMod 2) : signValue a ^ 2 = 1 := by
  rcases zmod2_cases a with h | h <;> subst a <;> decide

theorem sourcePhi_coboundary (i : Fin 2) (u v w : D i) :
    (sourcePhi i (u+v) w).val =
      (sourcePhi i u (v+w)).val * (sourcePhi i u v).val * (sourcePhi i v w).val *
        (-1 : Int)^(tripleWeight u.val v.val w.val) := by
  have he := congrArg signValue (codeFactor_coboundary i u v w)
  simp only [signValue_add,signValue_natCast] at he
  change signValue (codeFactor i (u+v) w) =
    signValue (codeFactor i u (v+w)) * signValue (codeFactor i u v) *
    signValue (codeFactor i v w) * _
  rw [← he]
  have hp := signValue_square (codeFactor i u v)
  have hq := signValue_square (codeFactor i v w)
  have hr := signValue_square (codeFactor i u (v+w))
  calc
    _ = signValue (codeFactor i u v)^2 * signValue (codeFactor i v w)^2 *
      signValue (codeFactor i u (v+w))^2 * signValue (codeFactor i (u+v) w) := by rw [hp,hq,hr]; ring
    _ = _ := by ring

noncomputable def sourceSignedMul (i : Fin 2) (a b : SourceSign × D i) : SourceSign × D i :=
  (signEquiv (signEquiv.symm a.1 + signEquiv.symm b.1 + codeFactor i a.2 b.2), a.2+b.2)

noncomputable def sourceSignRepresentation (i : Fin 2) : CommonLoop ≃ (SourceSign × D i) :=
  (representationEquiv i).trans (Equiv.prodCongr signEquiv (Equiv.refl _))

theorem sourceSignRepresentation_mul (i : Fin 2) (a b : CommonLoop) :
    sourceSignRepresentation i (commonMul a b) =
      sourceSignedMul i (sourceSignRepresentation i a) (sourceSignRepresentation i b) := by
  rw [sourceSignRepresentation,Equiv.trans_apply,representation_multiplicative]
  apply Prod.ext
  · simp [sourceSignedMul,representationEquiv,signedCodeMul]
  · rfl

theorem sourceSignedMul_sign (i : Fin 2) (a b : SourceSign × D i) :
    (sourceSignedMul i a b).1.val = a.1.val * b.1.val * (sourcePhi i a.2 b.2).val := by
  change signValue (_+_+_) = _
  rw [signValue_add,signValue_add]
  have ha := congrArg Subtype.val (signEquiv.apply_symm_apply a.1)
  have hb := congrArg Subtype.val (signEquiv.apply_symm_apply b.1)
  change signValue (signEquiv.symm a.1) = a.1.val at ha
  change signValue (signEquiv.symm b.1) = b.1.val at hb
  rw [ha,hb]
  rfl

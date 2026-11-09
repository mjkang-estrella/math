import CodeLoopLoop
import CodeLoopWeight
import CodeLoopIntersections
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Explicit multiplicative bijections. The weight factor-set axioms are separate obligations. -/

theorem D_rank_seven (i : Fin 2) : Module.finrank (ZMod 2) (D i) = 7 := by
  rw [← (parametersEquiv i).finrank_eq, Module.finrank_prod]
  simp [W4, W3]

noncomputable def codeParameters (i : Fin 2) (v : D i) : W4 × W3 :=
  (parametersEquiv i).symm v

noncomputable def codeFactor (i : Fin 2) (v w : D i) : ZMod 2 :=
  codeLoopF (codeParameters i v).2 (codeParameters i w).2

noncomputable def signedCodeMul (i : Fin 2) (a b : ZMod 2 × D i) : ZMod 2 × D i :=
  (a.1 + b.1 + codeFactor i a.2 b.2, a.2 + b.2)

noncomputable def representationEquiv (i : Fin 2) : CommonLoop ≃ (ZMod 2 × D i) :=
  Equiv.prodCongr (Equiv.refl _) (parametersEquiv i).toEquiv

theorem representation_multiplicative (i : Fin 2) (a b : CommonLoop) :
    representationEquiv i (commonMul a b) =
      signedCodeMul i (representationEquiv i a) (representationEquiv i b) := by
  apply Prod.ext
  · simp [representationEquiv, signedCodeMul, codeFactor, codeParameters, commonMul]
  · exact (parametersEquiv i).map_add a.2 b.2

theorem codeFactor_zero_left (i : Fin 2) (v : D i) : codeFactor i 0 v = 0 := by
  simp [codeFactor,codeParameters,codeLoopF_zero_left]

theorem codeFactor_zero_right (i : Fin 2) (v : D i) : codeFactor i v 0 = 0 := by
  simp [codeFactor,codeParameters,codeLoopF_zero_right]

theorem signedCode_moufang (i : Fin 2) (a b c : ZMod 2 × D i) :
    signedCodeMul i (signedCodeMul i a b) (signedCodeMul i c a) =
      signedCodeMul i a (signedCodeMul i (signedCodeMul i b c) a) := by
  obtain ⟨a,rfl⟩ := (representationEquiv i).surjective a
  obtain ⟨b,rfl⟩ := (representationEquiv i).surjective b
  obtain ⟨c,rfl⟩ := (representationEquiv i).surjective c
  simp only [← representation_multiplicative]
  exact congrArg (representationEquiv i) (common_moufang a b c)

theorem signedCode_nonassociative (i : Fin 2) :
    ¬ ∀ a b c, signedCodeMul i (signedCodeMul i a b) c =
      signedCodeMul i a (signedCodeMul i b c) := by
  intro h
  apply common_nonassociative
  intro a b c
  apply (representationEquiv i).injective
  simpa only [representation_multiplicative] using
    h (representationEquiv i a) (representationEquiv i b) (representationEquiv i c)


theorem dval_codeParameters (i : Fin 2) (v : D i) :
    dval i (codeParameters i v).1 (codeParameters i v).2 = v.val := by
  exact congrArg Subtype.val ((parametersEquiv i).apply_symm_apply v)

theorem source_diagonal_parity (i : Fin 2) (v : D i) :
    ((wordWeight v.val / 4 : Nat) : ZMod 2) = codeLoopQ (codeParameters i v).2 := by
  rw [← dval_codeParameters i v]
  exact dval_diagonal_parity i _ _

theorem codeFactor_diagonal (i : Fin 2) (v : D i) :
    codeFactor i v v = ((wordWeight v.val / 4 : Nat) : ZMod 2) := by
  rw [source_diagonal_parity]
  exact codeLoopF_self _

theorem codeFactor_symmetry (i : Fin 2) (v w : D i) :
    codeFactor i v w + codeFactor i w v = ((pairWeight v.val w.val / 2 : Nat) : ZMod 2) := by
  rw [pair_parity_of_weights v.val w.val (D_doubly_even i v) (D_doubly_even i w)
    (D_doubly_even i (v+w))]
  change codeLoopF _ _ + codeLoopF _ _ =
    ((wordWeight (v+w).val / 4 : Nat) : ZMod 2) + _ + _
  rw [source_diagonal_parity,source_diagonal_parity,source_diagonal_parity]
  simp only [codeParameters, map_add,Prod.snd_add]
  exact codeLoopF_symmetry _ _

theorem codeFactor_coboundary (i : Fin 2) (u v w : D i) :
    codeFactor i u v + codeFactor i (u+v) w + codeFactor i v w + codeFactor i u (v+w) =
      (tripleWeight u.val v.val w.val : ZMod 2) := by
  rw [triple_parity_of_weights u.val v.val w.val
    (D_doubly_even i u) (D_doubly_even i v) (D_doubly_even i w)
    (D_doubly_even i (u+v)) (D_doubly_even i (u+w)) (D_doubly_even i (v+w))
    (D_doubly_even i (u+v+w))]
  change codeFactor i u v + codeFactor i (u+v) w + codeFactor i v w + codeFactor i u (v+w) =
    ((wordWeight (u+v+w).val / 4 : Nat) : ZMod 2) +
    ((wordWeight u.val / 4 : Nat) : ZMod 2) +
    ((wordWeight v.val / 4 : Nat) : ZMod 2) +
    ((wordWeight w.val / 4 : Nat) : ZMod 2) +
    ((wordWeight (u+v).val / 4 : Nat) : ZMod 2) +
    ((wordWeight (u+w).val / 4 : Nat) : ZMod 2) +
    ((wordWeight (v+w).val / 4 : Nat) : ZMod 2)
  simp only [source_diagonal_parity,codeFactor,codeParameters,map_add,Prod.snd_add]
  exact (codeLoopQ_cubic _ _ _).symm

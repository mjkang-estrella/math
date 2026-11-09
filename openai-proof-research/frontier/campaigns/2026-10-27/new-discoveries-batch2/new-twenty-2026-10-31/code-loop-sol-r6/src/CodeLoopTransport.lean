import CodeLoopFin50

noncomputable section

theorem sameColumn50 (i : Fin 2) (c d : Fin 50) :
    (binaryCodeSetoid (D50 i)).r c d ↔
      SameColumn i ((coordEquiv50 i).symm c) ((coordEquiv50 i).symm d) := by
  constructor
  · intro h v hv
    exact h (transport50 i v) ⟨v,hv,rfl⟩
  · intro h v hv
    have hh := h ((transport50 i).symm v) ((mem_D50 i v).mp hv)
    change v (coordEquiv50 i ((coordEquiv50 i).symm c)) =
      v (coordEquiv50 i ((coordEquiv50 i).symm d)) at hh
    simpa using hh

def classesEquiv50 (i : Fin 2) : Quotient (binaryCodeSetoid (D50 i)) ≃ ColumnClass i where
  toFun := Quotient.map (coordEquiv50 i).symm (fun _ _ h => (sameColumn50 i _ _).mp h)
  invFun := Quotient.map (coordEquiv50 i) (fun c d h => by
    apply (sameColumn50 i _ _).mpr
    change SameColumn i c d at h
    simpa using h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ c =>
      change Quotient.mk _ _ = Quotient.mk _ c
      simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ c =>
      change Quotient.mk _ _ = Quotient.mk _ c
      simp

def positionsEquiv50 (i : Fin 2) (q : Quotient (binaryCodeSetoid (D50 i))) :
    binaryClassPositions (D50 i) q ≃ ClassPositions i (classesEquiv50 i q) where
  toFun c := ⟨(coordEquiv50 i).symm c.val, congrArg (classesEquiv50 i) c.property⟩
  invFun c := ⟨coordEquiv50 i c.val, by
    apply (classesEquiv50 i).injective
    change Quotient.mk (coordinateSetoid i) ((coordEquiv50 i).symm (coordEquiv50 i c.val)) = _
    simpa using c.property⟩
  left_inv c := by apply Subtype.ext; exact (coordEquiv50 i).apply_symm_apply c.val
  right_inv c := by apply Subtype.ext; exact (coordEquiv50 i).symm_apply_apply c.val

@[instance_reducible] def classesFintype50 (i : Fin 2) : Fintype (Quotient (binaryCodeSetoid (D50 i))) :=
  Fintype.ofEquiv (ColumnClass i) (classesEquiv50 i).symm

@[instance_reducible] def positionsFintype50 (i : Fin 2) (q : Quotient (binaryCodeSetoid (D50 i))) :
    Fintype (binaryClassPositions (D50 i) q) :=
  Fintype.ofEquiv (ClassPositions i (classesEquiv50 i q)) (positionsEquiv50 i q).symm

theorem reduced50 (i : Fin 2) (q : Quotient (binaryCodeSetoid (D50 i))) :
    @Fintype.card _ (positionsFintype50 i q) < 8 := by
  let := positionsFintype50 i q
  rw [Fintype.card_congr (positionsEquiv50 i q)]
  exact D_reduced i _

theorem codeType50_eq (i : Fin 2) :
    binaryCodeType (D50 i) (classesFintype50 i) (positionsFintype50 i) = codeType i := by
  let := classesFintype50 i
  let := positionsFintype50 i
  unfold binaryCodeType codeType
  have hc : ∀ q, Fintype.card (binaryClassPositions (D50 i) q) =
      Fintype.card (ClassPositions i (classesEquiv50 i q)) :=
    fun q => Fintype.card_congr (positionsEquiv50 i q)
  simp_rw [hc]
  have he : (Finset.univ : Finset (Quotient (binaryCodeSetoid (D50 i)))).map
      (classesEquiv50 i).toEmbedding = Finset.univ := by ext a; simp
  have hm := congrArg Finset.val he
  rw [← hm]
  change Multiset.map (fun q => Fintype.card (ClassPositions i (classesEquiv50 i q))) Finset.univ.val =
    Multiset.map (fun q => Fintype.card (ClassPositions i q))
      (Multiset.map (classesEquiv50 i) Finset.univ.val)
  rw [Multiset.map_map]
  rfl


theorem pairWeight_transport50 (i : Fin 2) (u v : Dcoord i → ZMod 2) :
    pairWeight (transport50 i u) (transport50 i v) = pairWeight u v := by
  have h := weight_pair_identity (transport50 i u) (transport50 i v)
  simp only [← (transport50 i).map_add,transport50_weight] at h
  have hr := weight_pair_identity u v
  omega

theorem tripleWeight_transport50 (i : Fin 2) (u v w : Dcoord i → ZMod 2) :
    tripleWeight (transport50 i u) (transport50 i v) (transport50 i w) = tripleWeight u v w := by
  have h := weight_triple_identity (transport50 i u) (transport50 i v) (transport50 i w)
  simp only [← (transport50 i).map_add,transport50_weight] at h
  have hr := weight_triple_identity u v w
  omega

theorem inverse50_val (i : Fin 2) (v : D50 i) :
    transport50 i ((subspaceEquiv50 i).symm v).val = v.val :=
  congrArg Subtype.val ((subspaceEquiv50 i).apply_symm_apply v)

theorem inverse50_weight (i : Fin 2) (v : D50 i) :
    wordWeight ((subspaceEquiv50 i).symm v).val = wordWeight v.val := by
  rw [← transport50_weight i, inverse50_val]

theorem inverse50_pair (i : Fin 2) (v w : D50 i) :
    pairWeight ((subspaceEquiv50 i).symm v).val ((subspaceEquiv50 i).symm w).val =
      pairWeight v.val w.val := by
  rw [← pairWeight_transport50 i,inverse50_val,inverse50_val]

theorem inverse50_triple (i : Fin 2) (u v w : D50 i) :
    tripleWeight ((subspaceEquiv50 i).symm u).val ((subspaceEquiv50 i).symm v).val
      ((subspaceEquiv50 i).symm w).val = tripleWeight u.val v.val w.val := by
  rw [← tripleWeight_transport50 i,inverse50_val,inverse50_val,inverse50_val]

def factor50 (i : Fin 2) : BinaryFactor (D50 i) where
  f v w := codeFactor i ((subspaceEquiv50 i).symm v) ((subspaceEquiv50 i).symm w)
  diagonal v := by rw [codeFactor_diagonal,inverse50_weight]
  symmetry v w := by rw [codeFactor_symmetry,inverse50_pair]
  zero_left v := by simp only [map_zero,codeFactor_zero_left]
  zero_right v := by simp only [map_zero,codeFactor_zero_right]
  coboundary u v w := by simp only [map_add]; rw [codeFactor_coboundary,inverse50_triple]

def representation50 (i : Fin 2) : CommonLoop ≃ (ZMod 2 × D50 i) :=
  (representationEquiv i).trans (Equiv.prodCongr (Equiv.refl _) (subspaceEquiv50 i).toEquiv)

theorem representation50_mul (i : Fin 2) (a b : CommonLoop) :
    representation50 i (commonMul a b) =
      (factor50 i).mul (representation50 i a) (representation50 i b) := by
  rw [representation50,Equiv.trans_apply,representation_multiplicative]
  apply Prod.ext
  · simp [factor50,BinaryFactor.mul,signedCodeMul]
  · exact (subspaceEquiv50 i).map_add _ _

theorem literal2019_refuted_on_fin50 : ¬ Literal2019Uniqueness := by
  intro h
  apply D50_no_permutation
  apply h (Fin 50) (Fin 50) inferInstance inferInstance (D50 0) (D50 1)
    (factor50 0) (factor50 1) (classesFintype50 0) (classesFintype50 1)
    (positionsFintype50 0) (positionsFintype50 1)
    (D50_doubly_even 0) (D50_doubly_even 1) (reduced50 0) (reduced50 1)
    CommonLoop commonMul common_isMoufangLoop
    ⟨representation50 0,representation50_mul 0⟩ ⟨representation50 1,representation50_mul 1⟩ rfl
  rw [codeType50_eq,codeType50_eq,exact_codeType,exact_codeType]


theorem full50_counterexample :
    (¬ Literal2019Uniqueness) ∧
    (¬ ∀ a b c : CommonLoop, commonMul (commonMul a b) c = commonMul a (commonMul b c)) ∧
    (∀ i : Fin 2,
      Module.finrank (ZMod 2) (D50 i) = 7 ∧
      (∀ v : D50 i, wordWeight v.val % 4 = 0) ∧
      (∀ c : Fin 50, ∃ v ∈ D50 i, v c = 1) ∧
      (binaryCodeType (D50 i) (classesFintype50 i) (positionsFintype50 i)).sort (· ≤ ·) =
        List.replicate 15 1 ++ List.replicate 7 5 ∧
      (∀ q, @Fintype.card _ (positionsFintype50 i q) < 8) ∧
      Represents (factor50 i) CommonLoop commonMul) ∧
    (¬ ∃ e : Equiv.Perm (Fin 50), ∀ v, v ∈ D50 0 ↔ (fun c => v (e.symm c)) ∈ D50 1) := by
  refine ⟨literal2019_refuted_on_fin50,common_nonassociative,?_,D50_no_permutation⟩
  intro i
  refine ⟨D50_rank i,D50_doubly_even i,D50_full_support i,?_,reduced50 i,
    ⟨representation50 i,representation50_mul i⟩⟩
  rw [codeType50_eq]
  exact exact_sortedCodeType i

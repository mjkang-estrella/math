import InterpFactors
set_option linter.unusedSectionVars false
namespace XorMagic
abbrev InterpAllowed {d : ℕ} (k : ℕ) (i : Fin d) :=
  {a : Four // if i.val < k then a ≠ 0 else a = 0}
abbrev InterpIndex (d k j : ℕ) := (Σ i : Fin d, InterpAllowed k i) ⊕ (Fin j × Four)
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {d c : ℕ}
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d) (H : MatchingDecomposition Gᶜ c)
def interpMate (k j : ℕ) (hj : j ≤ c) : InterpIndex d k j → (V × Four) → (V × Four)
  | .inl ia => blockMate F (T.matchingChart F) ia.1 ia.2.1
  | .inr ia => blockMate H (fun _ _ => Equiv.refl _) ⟨ia.1.val,lt_of_lt_of_le ia.1.isLt hj⟩ ia.2

theorem interpMate_involutive (k j : ℕ) (hj : j ≤ c) (i : InterpIndex d k j) :
    Function.Involutive (T.interpMate F H k j hj i) := by
  rcases i with ia | ia
  · exact blockMate_involutive F _ _ _
  · exact blockMate_involutive H (fun _ _ => Equiv.refl _) _ _
theorem interpMate_no_fixed (k j : ℕ) (hj : j ≤ c) (i : InterpIndex d k j) (p : V × Four) :
    T.interpMate F H k j hj i p ≠ p := by
  rcases i with ia | ia
  · exact blockMate_no_fixed F _ _ _ p
  · exact blockMate_no_fixed H (fun _ _ => Equiv.refl _) _ _ p

theorem interpMate_distinct (k j : ℕ) (hj : j ≤ c) (p : V × Four) :
    Function.Injective (fun i => T.interpMate F H k j hj i p) := by
  intro i l he
  rcases i with ⟨i,a⟩ | ⟨i,a⟩ <;> rcases l with ⟨l,b⟩ | ⟨l,b⟩
  · have h : (i,a.1) = (l,b.1) := blockMate_distinct F (T.matchingChart F) p (by exact he)
    have hi : i = l := congrArg Prod.fst h
    subst l
    exact congrArg Sum.inl (by congr 1; exact Subtype.ext (by simpa only using congrArg Prod.snd h))
  · have hv : F.mate i p.1 = H.mate ⟨l.val,lt_of_lt_of_le l.isLt hj⟩ p.1 := congrArg Prod.fst he
    have hg := (F.cover p.1 _).mpr ⟨i,rfl⟩
    have hh := (H.cover p.1 _).mpr ⟨⟨l.val,lt_of_lt_of_le l.isLt hj⟩,rfl⟩
    exact False.elim (hh.2 (hv ▸ hg))
  · have hv : H.mate ⟨i.val,lt_of_lt_of_le i.isLt hj⟩ p.1 = F.mate l p.1 := congrArg Prod.fst he
    have hg := (F.cover p.1 _).mpr ⟨l,rfl⟩
    have hh := (H.cover p.1 _).mpr ⟨⟨i.val,lt_of_lt_of_le i.isLt hj⟩,rfl⟩
    exact False.elim (hh.2 (hv.symm ▸ hg))
  · have h : ((⟨i.val,lt_of_lt_of_le i.isLt hj⟩ : Fin c),a) = ((⟨l.val,lt_of_lt_of_le l.isLt hj⟩ : Fin c),b) :=
      blockMate_distinct H (fun _ _ => Equiv.refl _) p (by exact he)
    exact congrArg Sum.inr (Prod.ext (Fin.ext (congrArg (fun z => z.1.val) h)) (by simpa only using congrArg Prod.snd h))

noncomputable def interpGraph (k j : ℕ) (hj : j ≤ c) : SimpleGraph (V × Four) :=
  involutionGraph (T.interpMate F H k j hj) (T.interpMate_involutive F H k j hj)
    (T.interpMate_no_fixed F H k j hj)
noncomputable instance (k j : ℕ) (hj : j ≤ c) : DecidableRel (T.interpGraph F H k j hj).Adj := Classical.decRel _
end EdgeTransport

theorem interpAllowed_card {d : ℕ} (k : ℕ) (i : Fin d) :
    Fintype.card (InterpAllowed k i) = if i.val < k then 3 else 1 := by
  by_cases h : i.val < k
  · simp only [InterpAllowed, h, ite_true]; decide +revert
  · simp [InterpAllowed,h]

theorem interp_count (d k : ℕ) (hk : k ≤ d) :
    (∑ i : Fin d, if i.val < k then 3 else 1) = d+2*k := by
  induction d generalizing k with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    simp
  | succ d ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.val_succ, Nat.succ_lt_succ_iff]
      rw [ih k (by omega)]
      omega

theorem interpIndex_card (d k j : ℕ) (hk : k ≤ d) :
    Fintype.card (InterpIndex d k j) = d+2*k+4*j := by
  simp only [InterpIndex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, show Fintype.card Four = 4 by decide]
  simp_rw [interpAllowed_card]
  rw [interp_count d k hk]
  omega

namespace EdgeTransport
theorem interpGraph_regular (T : EdgeTransport G) (F : MatchingDecomposition G d)
    (H : MatchingDecomposition Gᶜ c) (k j : ℕ) (hk : k ≤ d) (hj : j ≤ c) :
    (T.interpGraph F H k j hj).IsRegularOfDegree (d+2*k+4*j) := by
  rw [← interpIndex_card d k j hk]
  exact involutionGraph_degree _ _ _ (T.interpMate_distinct F H k j hj)
end EdgeTransport
end XorMagic

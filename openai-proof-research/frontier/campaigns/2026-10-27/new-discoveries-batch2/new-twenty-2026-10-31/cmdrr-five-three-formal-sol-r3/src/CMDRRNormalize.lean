import CMDRRCounts
import CMDRRSourceTransport

open scoped Classical
namespace CMDRR.Matching
variable {M W : Type} (s : CMDRR.Matching M W)
abbrev Pairs := {p : M × W // s.spouse p.1 p.2}
abbrev SingleMen := {m : M // s.SingleMan m}
abbrev SingleWomen := {w : W // s.SingleWoman w}

def maleProjection : s.Pairs ⊕ s.SingleMen → M
  | .inl p => p.1.1
  | .inr m => m.1

def femaleProjection : s.Pairs ⊕ s.SingleWomen → W
  | .inl p => p.1.2
  | .inr w => w.1

 theorem maleProjection_bijective : Function.Bijective s.maleProjection := by
  constructor
  · intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [maleProjection] at he
        have hw := s.right_unique _ _ _ a.2 (he.symm ▸ b.2)
        exact congrArg Sum.inl (Subtype.ext (Prod.ext he hw))
      | inr b =>
        simp only [maleProjection] at he
        exact (b.2 ⟨a.1.2,he ▸ a.2⟩).elim
    | inr a =>
      cases b with
      | inl b =>
        simp only [maleProjection] at he
        exact (a.2 ⟨b.1.2,he.symm ▸ b.2⟩).elim
      | inr b =>
        simp only [maleProjection] at he
        exact congrArg Sum.inr (Subtype.ext he)
  · intro m
    by_cases hm : ∃ w, s.spouse m w
    · obtain ⟨w,hw⟩ := hm
      exact ⟨.inl ⟨(m,w),hw⟩,rfl⟩
    · exact ⟨.inr ⟨m,hm⟩,rfl⟩

 theorem femaleProjection_bijective : Function.Bijective s.femaleProjection := by
  constructor
  · intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [femaleProjection] at he
        have hm := s.left_unique _ _ _ a.2 (he.symm ▸ b.2)
        exact congrArg Sum.inl (Subtype.ext (Prod.ext hm he))
      | inr b =>
        simp only [femaleProjection] at he
        exact (b.2 ⟨a.1.1,he ▸ a.2⟩).elim
    | inr a =>
      cases b with
      | inl b =>
        simp only [femaleProjection] at he
        exact (a.2 ⟨b.1.1,he.symm ▸ b.2⟩).elim
      | inr b =>
        simp only [femaleProjection] at he
        exact congrArg Sum.inr (Subtype.ext he)
  · intro w
    by_cases hw : ∃ m, s.spouse m w
    · obtain ⟨m,hm⟩ := hw
      exact ⟨.inl ⟨(m,w),hm⟩,rfl⟩
    · exact ⟨.inr ⟨w,hw⟩,rfl⟩

noncomputable def maleSplit : s.Pairs ⊕ s.SingleMen ≃ M :=
  Equiv.ofBijective s.maleProjection s.maleProjection_bijective
noncomputable def femaleSplit : s.Pairs ⊕ s.SingleWomen ≃ W :=
  Equiv.ofBijective s.femaleProjection s.femaleProjection_bijective

 theorem split_spouse (a : s.Pairs ⊕ s.SingleMen) (b : s.Pairs ⊕ s.SingleWomen) :
    s.spouse (s.maleSplit a) (s.femaleSplit b) ↔
      ∃ p : s.Pairs, a = .inl p ∧ b = .inl p := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      constructor
      · intro hs
        have hw := s.right_unique _ _ _ a.2 hs
        have hm := s.left_unique _ _ _ hs b.2
        have he : a = b := Subtype.ext (Prod.ext hm hw)
        exact ⟨a,rfl,congrArg Sum.inl he.symm⟩
      · rintro ⟨p,he,hf⟩
        have ha : a = p := Sum.inl.inj he
        have hb : b = p := Sum.inl.inj hf
        subst a; subst b
        exact p.2
    | inr b =>
      constructor
      · intro hs; exact (b.2 ⟨a.1.1,hs⟩).elim
      · rintro ⟨p,_,hf⟩; cases hf
  | inr a =>
    constructor
    · intro hs; exact (a.2 ⟨s.femaleSplit b,hs⟩).elim
    · rintro ⟨p,he,_⟩; cases he

variable [Fintype M] [Fintype W]
 theorem singles_card (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : CMDRR.count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    Fintype.card s.Pairs = 3 ∧ Fintype.card s.SingleMen = 2 ∧
      Fintype.card s.SingleWomen = 2 := by
  have hp : Fintype.card s.Pairs = 3 := by rw [CMDRR.count_eq_card] at hs; exact hs
  have he := Fintype.card_congr s.maleSplit
  have hf := Fintype.card_congr s.femaleSplit
  rw [Fintype.card_sum,hm,hp] at he
  rw [Fintype.card_sum,hw,hp] at hf
  exact ⟨hp,by omega,by omega⟩

 theorem normalized_labels (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : CMDRR.count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    ∃ (e : M ≃ (Fin 3 ⊕ Fin 2)) (f : W ≃ (Fin 3 ⊕ Fin 2)),
      ∀ m w, s.spouse m w ↔ ∃ i : Fin 3, e m = .inl i ∧ f w = .inl i := by
  obtain ⟨hp,hm2,hw2⟩ := s.singles_card hm hw hs
  let ep : s.Pairs ≃ Fin 3 := Fintype.equivFinOfCardEq hp
  let em : s.SingleMen ≃ Fin 2 := Fintype.equivFinOfCardEq hm2
  let ew : s.SingleWomen ≃ Fin 2 := Fintype.equivFinOfCardEq hw2
  let e := s.maleSplit.symm.trans (Equiv.sumCongr ep em)
  let f := s.femaleSplit.symm.trans (Equiv.sumCongr ep ew)
  refine ⟨e,f,?_⟩
  intro m w
  obtain ⟨a,rfl⟩ := s.maleSplit.surjective m
  obtain ⟨b,rfl⟩ := s.femaleSplit.surjective w
  rw [s.split_spouse]
  simp only [e, f, Equiv.trans_apply, Equiv.symm_apply_apply]
  cases a <;> cases b <;> simp

end CMDRR.Matching

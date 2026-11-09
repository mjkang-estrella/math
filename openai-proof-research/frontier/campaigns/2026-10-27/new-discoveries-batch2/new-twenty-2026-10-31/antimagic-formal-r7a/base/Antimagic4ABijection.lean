import Antimagic4AHigh
namespace Antimagic.Round4A
open Round3
abbrev Places (s : ℕ) := (Fin (2 * s) ⊕ Fin (2 * s)) ⊕ (Fin (2 * s - 1) × Fin (2 * s))
def totalEntry (s : ℕ) : Places s → ℕ
  | .inl p => lowEntry s p
  | .inr p => 4 * s + highEntry s p.1.val p.2.val

theorem totalEntry_range (s : ℕ) (hs : 2 ≤ s) (p : Places s) :
    1 ≤ totalEntry s p ∧ totalEntry s p ≤ 4 * s + (2 * s) * (2 * s - 1) := by
  cases p with
  | inl p => have := lowEntry_range s hs p; simp only [totalEntry]; omega
  | inr p => have := highEntry_range s p.1.val p.2.val hs p.1.isLt p.2.isLt
             simp only [totalEntry]; omega

theorem totalEntry_injective (s : ℕ) (hs : 2 ≤ s) : Function.Injective (totalEntry s) := by
  intro p q he
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (lowEntry_injective s hs he)
    | inr q =>
      have := lowEntry_range s hs p
      have := highEntry_range s q.1.val q.2.val hs q.1.isLt q.2.isLt
      simp only [totalEntry] at he; omega
  | inr p =>
    cases q with
    | inl q =>
      have := lowEntry_range s hs q
      have := highEntry_range s p.1.val p.2.val hs p.1.isLt p.2.isLt
      simp only [totalEntry] at he; omega
    | inr q =>
      apply congrArg Sum.inr
      apply highEntry_injective s hs
      exact Nat.add_left_cancel he

def totalMap (s : ℕ) (hs : 2 ≤ s) (p : Places s) : Fin (4 * s + (2 * s) * (2 * s - 1)) :=
  ⟨totalEntry s p - 1, by have := totalEntry_range s hs p; omega⟩
theorem totalMap_bijective (s : ℕ) (hs : 2 ≤ s) : Function.Bijective (totalMap s hs) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q h
    apply totalEntry_injective s hs
    have hp := totalEntry_range s hs p
    have hq := totalEntry_range s hs q
    have he := congrArg Fin.val h
    change totalEntry s p - 1 = totalEntry s q - 1 at he
    omega
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [Nat.mul_comm (2 * s - 1) (2 * s)]
    omega

def placeVertex (s : ℕ) (hs : 2 ≤ s) : Places s → Nonroot (2 * s) 2
  | .inl (.inl i) => ⟨⟨⟨1, by omega⟩, ⟨i.val, by simpa only [pow_one] using i.isLt⟩⟩, by change 0 < 1; omega⟩
  | .inl (.inr j) => ⟨⟨⟨2, by omega⟩, ⟨j.val, by have := j.isLt; nlinarith⟩⟩, by change 0 < 2; omega⟩
  | .inr p => ⟨⟨⟨2, by omega⟩, ⟨(2 * s) * (p.1.val + 1) + p.2.val, by
      have ha := p.1.isLt
      have hj := p.2.isLt
      have h := Nat.mul_le_mul_left (2 * s) (show p.1.val + 2 ≤ 2 * s by omega)
      nlinarith⟩⟩, by change 0 < 2; omega⟩

theorem vertex_ext {t n : ℕ} {u v : Nonroot t n}
    (hh : u.val.1.val = v.val.1.val) (hi : u.val.2.val = v.val.2.val) : u = v := by
  apply Subtype.ext
  apply Sigma.ext (Fin.ext hh)
  exact (Fin.heq_ext_iff (by exact congrArg (fun h => t ^ h) hh)).mpr hi

theorem placeVertex_surjective (s : ℕ) (hs : 2 ≤ s) : Function.Surjective (placeVertex s hs) := by
  intro v
  have hv := v.val.1.isLt
  have hv0 : 0 < v.val.1.val := v.property
  have hi := v.val.2.isLt
  by_cases hh : v.val.1.val = 1
  · refine ⟨.inl (.inl ⟨v.val.2.val, by simpa only [hh, pow_one] using hi⟩), ?_⟩
    exact vertex_ext hh.symm rfl
  · have hh2 : v.val.1.val = 2 := by omega
    have hib : v.val.2.val < (2 * s) ^ 2 := by simpa only [hh2] using hi
    by_cases hsmall : v.val.2.val < 2 * s
    · refine ⟨.inl (.inr ⟨v.val.2.val, hsmall⟩), ?_⟩
      apply vertex_ext hh2.symm; rfl
    · have ht : 0 < 2 * s := by omega
      have hd : v.val.2.val / (2 * s) < 2 * s := by
        apply (Nat.div_lt_iff_lt_mul ht).mpr
        simpa only [pow_two] using hib
      have hd0 : 0 < v.val.2.val / (2 * s) := Nat.div_pos (by omega) ht
      refine ⟨.inr (⟨v.val.2.val / (2 * s) - 1, by omega⟩,
        ⟨v.val.2.val % (2 * s), Nat.mod_lt _ ht⟩), ?_⟩
      apply vertex_ext hh2.symm
      change (2 * s) * (v.val.2.val / (2 * s) - 1 + 1) + v.val.2.val % (2 * s) = _
      rw [Nat.sub_add_cancel hd0]
      exact Nat.div_add_mod _ _

theorem placeVertex_label (s : ℕ) (hs : 2 ≤ s) (p : Places s) :
    label (2 * s) 2 (placeVertex s hs p).val.1.val (placeVertex s hs p).val.2.val = totalEntry s p := by
  have hl (h i : ℕ) : label (2 * s) 2 h i = depthTwoLabel (2 * s) h i := by
    simp only [label, show ¬ (2 = 1) by decide, show ¬ (2 * s = 2) by omega, ite_false, ite_true]
  rw [hl]
  cases p with
  | inl p =>
    cases p with
    | inl i => exact lowEntry_root s i
    | inr j => exact lowEntry_special s hs j
  | inr p => exact highEntry_formula s _ _ hs p.1.isLt p.2.isLt

theorem formula_range (s : ℕ) (hs : 2 ≤ s) (v : Nonroot (2 * s) 2) :
    1 ≤ label (2 * s) 2 v.val.1.val v.val.2.val ∧
    label (2 * s) 2 v.val.1.val v.val.2.val ≤ 4 * s + (2 * s) * (2 * s - 1) := by
  obtain ⟨p, rfl⟩ := placeVertex_surjective s hs v
  rw [placeVertex_label]
  exact totalEntry_range s hs p

def formulaMap (s : ℕ) (hs : 2 ≤ s) (v : Nonroot (2 * s) 2) :
    Fin (4 * s + (2 * s) * (2 * s - 1)) :=
  ⟨label (2 * s) 2 v.val.1.val v.val.2.val - 1, by have := formula_range s hs v; omega⟩

theorem formulaMap_bijective (s : ℕ) (hs : 2 ≤ s) : Function.Bijective (formulaMap s hs) := by
  have hc (p : Places s) : formulaMap s hs (placeVertex s hs p) = totalMap s hs p := by
    apply Fin.ext
    exact congrArg (fun x => x - 1) (placeVertex_label s hs p)
  constructor
  · intro v w he
    obtain ⟨p, rfl⟩ := placeVertex_surjective s hs v
    obtain ⟨q, rfl⟩ := placeVertex_surjective s hs w
    rw [hc, hc] at he
    exact congrArg (placeVertex s hs) ((totalMap_bijective s hs).1 he)
  · intro x
    obtain ⟨p, hp⟩ := (totalMap_bijective s hs).2 x
    exact ⟨placeVertex s hs p, (hc p).trans hp⟩

noncomputable def depthTwoLabeling (s : ℕ) (hs : 2 ≤ s) : Labeling (tree (2 * s) 2) :=
  let e := Equiv.ofBijective _ (formulaMap_bijective s hs)
  (incomingEquiv (by omega : 0 < 2 * s)).symm.trans (e.trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv (by omega : 0 < 2 * s)),
      Fintype.card_congr e, Fintype.card_fin])))

theorem depthTwoLabeling_label (s : ℕ) (hs : 2 ≤ s) (v : Nonroot (2 * s) 2) :
    (depthTwoLabeling s hs (incomingEdge (by omega) v)).val + 1 =
      label (2 * s) 2 v.val.1.val v.val.2.val := by
  change (depthTwoLabeling s hs ((incomingEquiv (by omega)) v)).val + 1 = _
  simp only [depthTwoLabeling, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_apply, Fin.val_cast]
  exact Nat.sub_add_cancel (formula_range s hs v).1

#print axioms formulaMap_bijective
#print axioms depthTwoLabeling_label
end Antimagic.Round4A

# Lean source appendix

Modules in dependency order. Each Lean block is byte-identical to its source.

### `ZigzagDefinitions.lean`

```lean
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Lattice
import Lean.Elab.Tactic.Omega

namespace Zigzag

/-- Vertex i is the source vertex v_(i+1). -/
def zigLt (n : ℕ) (a b : Fin n) : Prop :=
  a.val % 2 = 0 ∧ (b.val = a.val + 1 ∨ a.val = b.val + 1)

instance (n : ℕ) : DecidableRel (zigLt n) := fun _ _ => inferInstanceAs
  (Decidable (_ ∧ (_ ∨ _)))

theorem zigLt_irrefl (n : ℕ) (a : Fin n) : ¬ zigLt n a a := by
  simp only [zigLt]
  omega

theorem zigLt_trans (n : ℕ) (a b c : Fin n)
    (hab : zigLt n a b) (hbc : zigLt n b c) : zigLt n a c := by
  obtain ⟨ha, hab⟩ := hab
  obtain ⟨hb, _⟩ := hbc
  omega

instance zigLt_strictOrder (n : ℕ) : IsStrictOrder (Fin n) (zigLt n) where
  irrefl := zigLt_irrefl n
  trans := zigLt_trans n

/-- The inverse is the source's order-preserving vertex-to-label map. -/
def IsLE {n : ℕ} (R : Fin n → Fin n → Prop) (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b, R a b → w.symm a < w.symm b

instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (w : Equiv.Perm (Fin n)) : Decidable (IsLE R w) :=
  inferInstanceAs (Decidable (∀ a b, R a b → w.symm a < w.symm b))

abbrev LinearExtensions {n : ℕ} (R : Fin n → Fin n → Prop) :=
  {w : Equiv.Perm (Fin n) // IsLE R w}

instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    Fintype (LinearExtensions R) := inferInstanceAs (Fintype {w // IsLE R w})

instance {n : ℕ} (R : Fin n → Fin n → Prop) : DecidableEq (LinearExtensions R) :=
  inferInstanceAs (DecidableEq {w // IsLE R w})

abbrev ZigzagLE (n : ℕ) := LinearExtensions (zigLt n)

def leftPos {n : ℕ} (i : ℕ) (hi : i + 1 < n) : Fin n := ⟨i, by omega⟩
def rightPos {n : ℕ} (i : ℕ) (hi : i + 1 < n) : Fin n := ⟨i + 1, hi⟩
def adjacentSwap {n : ℕ} (i : ℕ) (hi : i + 1 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap (leftPos i hi) (rightPos i hi)
def rawSwap {n : ℕ} (i : ℕ) (hi : i + 1 < n)
    (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (adjacentSwap i hi).trans w

@[simp] theorem rawSwap_twice {n : ℕ} (i : ℕ) (hi : i + 1 < n)
    (w : Equiv.Perm (Fin n)) : rawSwap i hi (rawSwap i hi w) = w := by
  ext x
  simp [rawSwap, adjacentSwap]

@[simp] theorem rawSwap_symm_apply {n : ℕ} (i : ℕ) (hi : i + 1 < n)
    (w : Equiv.Perm (Fin n)) (x : Fin n) :
    (rawSwap i hi w).symm x = adjacentSwap i hi (w.symm x) := rfl

theorem adjacentSwap_lt {n : ℕ} (i : ℕ) (hi : i + 1 < n)
    (a b : Fin n) (hab : a < b)
    (hex : ¬ (a = leftPos i hi ∧ b = rightPos i hi)) :
    adjacentSwap i hi a < adjacentSwap i hi b := by
  have hl : (leftPos i hi).val = i := rfl
  have hr : (rightPos i hi).val = i + 1 := rfl
  have hex' : ¬ (a.val = i ∧ b.val = i + 1) := by
    rintro ⟨ha, hb⟩
    exact hex ⟨Fin.ext ha, Fin.ext hb⟩
  simp only [adjacentSwap, Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> try omega
  all_goals simp_all

def incomparable {n : ℕ} (R : Fin n → Fin n → Prop)
    (i : ℕ) (hi : i + 1 < n) (w : Equiv.Perm (Fin n)) : Prop :=
  ¬ R (w (leftPos i hi)) (w (rightPos i hi)) ∧
  ¬ R (w (rightPos i hi)) (w (leftPos i hi))

instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : Equiv.Perm (Fin n)) :
    Decidable (incomparable R i hi w) := inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem rawSwap_isLE_iff {n : ℕ} (R : Fin n → Fin n → Prop)
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R) :
    IsLE R (rawSwap i hi w.val) ↔ incomparable R i hi w.val := by
  constructor
  · intro h
    constructor
    · intro hrel
      have hh := h _ _ hrel
      simp [rawSwap_symm_apply, adjacentSwap, leftPos, rightPos, Fin.lt_def] at hh
      omega
    · intro hrel
      have hh := w.property _ _ hrel
      simp [leftPos, rightPos, Fin.lt_def] at hh
      omega
  · intro h a b hab
    rw [rawSwap_symm_apply, rawSwap_symm_apply]
    apply adjacentSwap_lt i hi _ _ (w.property _ _ hab)
    rintro ⟨ha, hb⟩
    apply h.1
    have ha' : w.val (leftPos i hi) = a := by rw [← ha]; simp
    have hb' : w.val (rightPos i hi) = b := by rw [← hb]; simp
    simpa only [ha', hb'] using hab

/-- Implemented by validity of the swapped word; rawSwap_isLE_iff proves the
    source's literal incomparability criterion, for every input word. -/
def moveFun {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R) : LinearExtensions R :=
  if h : IsLE R (rawSwap i hi w.val) then ⟨rawSwap i hi w.val, h⟩ else w

theorem moveFun_involutive {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) : Function.Involutive (moveFun R i hi) := by
  intro w
  by_cases h : IsLE R (rawSwap i hi w.val)
  · have hval : (moveFun R i hi w).val = rawSwap i hi w.val := by
      simp only [moveFun, h, dite_true]
    apply Subtype.ext
    simp [moveFun, h, w.property]
  · simp only [moveFun, h, dite_false]

def move {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) : Equiv.Perm (LinearExtensions R) :=
  (moveFun_involutive R i hi).toPerm (moveFun R i hi)

theorem move_apply {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R) :
    (move R i hi w).val =
      if incomparable R i hi w.val then rawSwap i hi w.val else w.val := by
  change (moveFun R i hi w).val = _
  unfold moveFun
  by_cases h : IsLE R (rawSwap i hi w.val)
  · simp only [h, dite_true, (rawSwap_isLE_iff R i hi w).mp h, ite_true]
  · have hh := (rawSwap_isLE_iff R i hi w).not.mp h
    simp only [h, dite_false, hh, ite_false]

theorem move_involutive {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) : Function.Involutive (move R i hi) :=
  moveFun_involutive R i hi

def bk (n : ℕ) (i : ℕ) (hi : i + 1 < n) : Equiv.Perm (ZigzagLE n) :=
  move (zigLt n) i hi

def BKgroup (n : ℕ) : Subgroup (Equiv.Perm (ZigzagLE n)) :=
  Subgroup.closure {g | ∃ i h, g = bk n i h}

theorem bk_mem (n i : ℕ) (hi : i + 1 < n) : bk n i hi ∈ BKgroup n :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

#print axioms zigLt_trans
#print axioms rawSwap_isLE_iff
#print axioms move_apply
#print axioms move_involutive
end Zigzag
```

### `ZigzagCounts.lean`

```lean
import ZigzagDefinitions

namespace Zigzag

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem card_zigzagLE_four : Fintype.card (ZigzagLE 4) = 5 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem card_zigzagLE_six : Fintype.card (ZigzagLE 6) = 61 := by decide

#print axioms card_zigzagLE_four
#print axioms card_zigzagLE_six
end Zigzag
```

### `ZigzagBases.lean`

```lean
import ZigzagCounts
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Zigzag
open Equiv Equiv.Perm

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem zero_symmetric : BKgroup 0 = ⊤ := by
  have hc : Fintype.card (ZigzagLE 0) ≤ 1 := by decide
  have : Subsingleton (ZigzagLE 0) := Fintype.card_le_one_iff_subsingleton.mp hc
  exact Subsingleton.elim _ _

theorem two_symmetric : BKgroup 2 = ⊤ := by
  have hc : Fintype.card (ZigzagLE 2) ≤ 1 := by decide
  have : Subsingleton (ZigzagLE 2) := Fintype.card_le_one_iff_subsingleton.mp hc
  exact Subsingleton.elim _ _

/-- Source words 1324,1342,3124,3142,3412, with 1 subtracted from each letter. -/
def wordFour (k : Fin 5) : Perm (Fin 4) where
  toFun := ![![0,2,1,3], ![0,2,3,1], ![2,0,1,3], ![2,0,3,1], ![2,3,0,1]] k
  invFun := ![![0,2,1,3], ![0,3,1,2], ![1,2,0,3], ![1,3,0,2], ![2,3,0,1]] k
  left_inv := by revert k; decide
  right_inv := by revert k; decide

def leFour (k : Fin 5) : ZigzagLE 4 := ⟨wordFour k, by revert k; decide⟩

theorem leFour_surjective : Function.Surjective leFour := by decide

theorem middle_generator_four : bk 4 1 (by decide) = swap (leFour 3) (leFour 4) :=
  by decide

def smallConj (k : Fin 5) : Perm (ZigzagLE 4) :=
  ![bk 4 0 (by decide) * bk 4 2 (by decide), bk 4 0 (by decide),
    bk 4 2 (by decide), 1, 1] k

theorem smallConj_mem (k : Fin 5) : smallConj k ∈ BKgroup 4 := by
  fin_cases k <;> dsimp only [smallConj]
  · exact (BKgroup 4).mul_mem (bk_mem 4 0 _) (bk_mem 4 2 _)
  · exact bk_mem 4 0 _
  · exact bk_mem 4 2 _
  · exact (BKgroup 4).one_mem
  · exact (BKgroup 4).one_mem

theorem smallConj_action : ∀ k : Fin 5, k ≠ 4 →
    smallConj k (leFour 3) = leFour k ∧ smallConj k (leFour 4) = leFour 4 := by decide

theorem four_symmetric : BKgroup 4 = ⊤ := by
  have hstar (x : ZigzagLE 4) : swap x (leFour 4) ∈ BKgroup 4 := by
    obtain ⟨k, rfl⟩ := leFour_surjective x
    by_cases hk : k = 4
    · subst k
      simpa only [Equiv.swap_self, ← Equiv.Perm.one_def] using (BKgroup 4).one_mem
    · have hmem := (BKgroup 4).mul_mem
        ((BKgroup 4).mul_mem (smallConj_mem k) (bk_mem 4 1 (by decide)))
        ((BKgroup 4).inv_mem (smallConj_mem k))
      rw [middle_generator_four, mul_swap_eq_swap_mul, mul_inv_cancel_right,
        (smallConj_action k hk).1, (smallConj_action k hk).2] at hmem
      exact hmem
  rw [eq_top_iff, ← closure_isSwap, Subgroup.closure_le]
  rintro g ⟨x, y, _, rfl⟩
  exact SubmonoidClass.swap_mem_trans (BKgroup 4) (hstar x)
    (by simpa only [Equiv.swap_comm] using hstar y)

#print axioms zero_symmetric
#print axioms two_symmetric
#print axioms four_symmetric
end Zigzag
```

### `SourceBridge.lean`

```lean
import ZigzagDefinitions

namespace Zigzag

theorem zigLt_comparable_iff (n : ℕ) (a b : Fin n) :
    (zigLt n a b ∨ zigLt n b a) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
  simp only [zigLt]
  omega

/-- Even Lean vertices, i.e. odd source vertices, are exactly the minima. -/
theorem minimal_iff_even (n : ℕ) (a : Fin n) :
    (∀ b, ¬ zigLt n b a) ↔ a.val % 2 = 0 := by
  constructor
  · intro h
    by_contra ha
    have hapos : 0 < a.val := by omega
    let b : Fin n := ⟨a.val - 1, by omega⟩
    apply h b
    change (a.val - 1) % 2 = 0 ∧ (a.val = (a.val - 1) + 1 ∨ _)
    omega
  · intro ha b hab
    obtain ⟨hb, hab⟩ := hab
    omega

/-- The source's vertex-to-label convention, with all labels decreased by one. -/
abbrev LabelLE (n : ℕ) :=
  {ell : Equiv.Perm (Fin n) // ∀ a b, zigLt n a b → ell a < ell b}

/-- The source explicitly identifies a label bijection with its inverse word.
    This formal bridge has no unproved equivalence of combinatorial models. -/
def sourceLabelBridge (n : ℕ) : ZigzagLE n ≃ LabelLE n where
  toFun w := ⟨w.val.symm, w.property⟩
  invFun ell := ⟨ell.val.symm, by simpa only [IsLE, Equiv.symm_symm] using ell.property⟩
  left_inv w := Subtype.ext (Equiv.symm_symm w.val)
  right_inv ell := Subtype.ext (Equiv.symm_symm ell.val)

/-- Source t_(i+1) interchanges labels i and i+1 in the label convention. -/
theorem bk_source_labels (n i : ℕ) (hi : i + 1 < n) (w : ZigzagLE n) :
    (sourceLabelBridge n (bk n i hi w)).val =
      if incomparable (zigLt n) i hi w.val then
        w.val.symm.trans (adjacentSwap i hi) else w.val.symm := by
  change (bk n i hi w).val.symm = _
  rw [show (bk n i hi w).val = _ from move_apply (zigLt n) i hi w]
  split_ifs <;> rfl

#print axioms zigLt_comparable_iff
#print axioms minimal_iff_even
#print axioms sourceLabelBridge
#print axioms bk_source_labels
end Zigzag
```

### `SectionFree.lean`

```lean
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Group.Pi.Basic

namespace Zigzag

/-- No subgroup has S as a quotient. This is equivalent to excluding S as a
    section, and avoids having to choose a quotient presentation. -/
def SectionFree (S G : Type*) [Group S] [Group G] : Prop :=
  ∀ (H : Subgroup G) (f : H →* S), ¬ Function.Surjective f

variable {S G B : Type*} [Group S] [Group G] [Group B]

theorem SectionFree.no_surjective (h : SectionFree S G) (f : G →* S) :
    ¬ Function.Surjective f := by
  intro hf
  apply h ⊤ (f.comp (⊤ : Subgroup G).subtype)
  intro s
  obtain ⟨g, rfl⟩ := hf s
  exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩

theorem sectionFree_of_card_lt [Finite G] (h : Nat.card G < Nat.card S) :
    SectionFree S G := by
  intro H f hf
  have hs := Nat.card_le_card_of_surjective f hf
  have hh := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  exact (not_le_of_gt h) (hs.trans hh)

theorem sectionFree_of_injective (f : G →* B) (hf : Function.Injective f)
    (hB : SectionFree S B) : SectionFree S G := by
  intro H q hq
  let e := H.equivMapOfInjective f hf
  exact hB (H.map f) (q.comp e.symm.toMonoidHom) (hq.comp e.symm.surjective)

theorem sectionFree_subgroup (h : SectionFree S G) (H : Subgroup G) :
    SectionFree S H :=
  sectionFree_of_injective H.subtype Subtype.val_injective h

theorem sectionFree_quotient (f : G →* B) (hf : Function.Surjective f)
    (hG : SectionFree S G) : SectionFree S B := by
  intro H q hq
  exact hG (H.comap f) (q.comp (f.subgroupComap H))
    (hq.comp (f.subgroupComap_surjective H hf))

/-- The simple-section dichotomy for an extension. No finiteness assumption is
    required here; simplicity is exactly what makes the image dichotomy work. -/
theorem sectionFree_extension [IsSimpleGroup S] (f : G →* B)
    (hker : SectionFree S f.ker) (hB : SectionFree S B) : SectionFree S G := by
  classical
  intro H q hq
  let p : H →* B := f.comp H.subtype
  let N : Subgroup H := p.ker
  have hnormal : (N.map q).Normal := (inferInstance : N.Normal).map q hq
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · have hle : p.rangeRestrict.ker ≤ q.ker := by
      intro x hx
      have hx' : x ∈ N := by simpa only [MonoidHom.ker_rangeRestrict] using hx
      have hmem : q x ∈ N.map q := ⟨x, hx', rfl⟩
      rw [hbot] at hmem
      exact hmem
    let q' : p.range →* S := p.rangeRestrict.liftOfSurjective
      p.rangeRestrict_surjective ⟨q, hle⟩
    have hq' : Function.Surjective q' := by
      intro s
      obtain ⟨x, rfl⟩ := hq s
      refine ⟨p.rangeRestrict x, ?_⟩
      exact p.rangeRestrict.liftOfRightInverse_comp_apply
        (Function.surjInv p.rangeRestrict_surjective)
        (Function.rightInverse_surjInv p.rangeRestrict_surjective) ⟨q, hle⟩ x
    exact (sectionFree_subgroup hB p.range).no_surjective q' hq'
  · let j : N →* f.ker :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.ker => z.val) hxy
    have hn : SectionFree S N := sectionFree_of_injective j hj hker
    apply hn.no_surjective (q.comp N.subtype)
    intro s
    have hs : s ∈ N.map q := by rw [htop]; trivial
    obtain ⟨x, hx, he⟩ := hs
    exact ⟨⟨x, hx⟩, he⟩

theorem sectionFree_prod {A C : Type*} [Group A] [Group C] [IsSimpleGroup S]
    (hA : SectionFree S A) (hC : SectionFree S C) : SectionFree S (A × C) := by
  let f : A × C →* A := MonoidHom.fst A C
  apply sectionFree_extension f _ hA
  let j : f.ker →* C := (MonoidHom.snd A C).comp f.ker.subtype
  apply sectionFree_of_injective j _ hC
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact x.property.trans y.property.symm
  · exact hxy

theorem sectionFree_of_subsingleton [Subsingleton G] [Nontrivial S] :
    SectionFree S G := by
  intro H f hf
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  obtain ⟨x, hx⟩ := hf s
  have hx1 : x = 1 := Subsingleton.elim _ _
  exact hs (by simpa only [hx1, map_one] using hx.symm)

theorem sectionFree_pi {J : Type*} [Finite J] [IsSimpleGroup S]
    (X : J → Type*) [∀ j, Group (X j)] (hX : ∀ j, SectionFree S (X j)) :
    SectionFree S (∀ j, X j) := by
  induction J using Finite.induction_empty_option with
  | @of_equiv J K e ih =>
    let f : (∀ k, X k) →* (∀ j, X (e j)) :=
      { toFun := fun x j => x (e j)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply sectionFree_of_injective f _ (ih (fun j => X (e j)) (fun j => hX (e j)))
    intro x y hxy
    funext k
    obtain ⟨j, rfl⟩ := e.surjective k
    exact congrFun hxy j
  | h_empty => exact sectionFree_of_subsingleton
  | @h_option J _ ih =>
    let f : (∀ k, X k) →* (X none × (∀ j, X (some j))) :=
      { toFun := fun x => (x none, fun j => x (some j))
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply sectionFree_of_injective f _ (sectionFree_prod (hX none)
      (ih (fun j => X (some j)) (fun j => hX (some j))))
    intro x y hxy
    funext k
    cases k with
    | none => exact congrArg Prod.fst hxy
    | some j => exact congrFun (congrArg Prod.snd hxy) j

#print axioms sectionFree_of_card_lt
#print axioms sectionFree_extension
#print axioms sectionFree_prod
#print axioms sectionFree_pi
end Zigzag
```

### `RemainingStatements.lean`

```lean
import ZigzagDefinitions
import Mathlib.GroupTheory.SpecificGroups.Alternating
import SectionFree
import Mathlib.Data.Finite.Perm

namespace Zigzag

/-- Literal generic BK group, also used for disconnected residual orders. -/
def relationBK {r : ℕ} (R : Fin r → Fin r → Prop) [DecidableRel R] :
    Subgroup (Equiv.Perm (LinearExtensions R)) :=
  Subgroup.closure {g | ∃ i h, g = move R i h}

/-- Position-to-vertex extensions of the j-th component. Components are
    identified by an arbitrary label c, and may be empty. -/
def ComponentLE {r k : ℕ} (R : Fin r → Fin r → Prop) (c : Fin r → Fin k)
    (j : Fin k) :=
  {w : Fin (Fintype.card {v : Fin r // c v = j}) ≃ {v : Fin r // c v = j} //
    ∀ a b, R a.val b.val → w.symm a < w.symm b}

/-- Exact §1.2 obligation, with every local extension type specified.
    This is a proposition, NOT a theorem or an assumed constant. The proved
    ShuffleSectionBound theorem supplies its algebraic part. -/
def LeftoverSectionBound : Prop :=
  ∀ (r k : ℕ) (R : Fin r → Fin r → Prop) [DecidableRel R]
    [IsStrictOrder (Fin r) R] (c : Fin r → Fin k),
    (∀ a b, R a b → c a = c b) →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      r.factorial < Nat.card S →
      (∀ j, (Nat.card (ComponentLE R c j)).factorial < Nat.card S) →
      SectionFree S (relationBK R)

/-- The main unproved induction step, proof §§2–5. -/
def AlternatingStep : Prop :=
  ∀ n, Even n → 6 ≤ n → BKgroup (n - 2) = ⊤ →
    alternatingGroup (ZigzagLE n) ≤ BKgroup n

/-- The parity obligation, source t_2 = Lean bk at index 1. -/
def OddStep : Prop :=
  ∀ n (h : 2 < n), Even n → 4 ≤ n → Equiv.Perm.sign (bk n 1 h) = -1

/-- The full, unrestricted target. This definition does not assert it. -/
def EvenConjecture : Prop := ∀ n, Even n → BKgroup n = ⊤

end Zigzag
```

### `ShuffleKernel.lean`

```lean
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-! The coordinatewise shuffle-kernel mechanism of proof §1.2.
This module deliberately does not assume any fence induction. -/
namespace Zigzag.Shuffle

open Equiv

variable {Sh J : Type*} {X : J → Type*}

abbrev State (Sh : Type*) (X : J → Type*) := Sh × (∀ j, X j)
abbrev Coordinates (Sh : Type*) (X : J → Type*) := ∀ _ : Sh, ∀ j, Perm (X j)

/-- A permutation can change the shuffle and, along that trajectory, apply
    separate permutations to the internal extension of each component. -/
def Skew (g : Perm (State Sh X)) : Prop :=
  ∃ (τ : Perm Sh) (f : Coordinates Sh X),
    ∀ s x, g (s, x) = (τ s, fun j => f s j (x j))

theorem skew_one : Skew (1 : Perm (State Sh X)) :=
  ⟨1, 1, fun _ _ => rfl⟩

theorem skew_mul {g h : Perm (State Sh X)} (hg : Skew g) (hh : Skew h) :
    Skew (g * h) := by
  obtain ⟨τ, f, hf⟩ := hg
  obtain ⟨υ, k, hk⟩ := hh
  refine ⟨τ * υ, fun s j => f (υ s) j * k s j, ?_⟩
  intro s x
  simp only [Perm.mul_apply, hk, hf]

theorem skew_inv {g : Perm (State Sh X)} (hg : Skew g) : Skew g⁻¹ := by
  obtain ⟨τ, f, hf⟩ := hg
  refine ⟨τ⁻¹, fun s j => (f (τ⁻¹ s) j)⁻¹, ?_⟩
  intro s x
  apply g.injective
  change g (g.symm (s, x)) = _
  rw [Equiv.apply_symm_apply, hf]
  simp

def skewSubgroup (Sh : Type*) (X : J → Type*) : Subgroup (Perm (State Sh X)) where
  carrier := Skew
  one_mem' := skew_one
  mul_mem' := skew_mul
  inv_mem' := skew_inv

theorem closure_le_skew (generators : Set (Perm (State Sh X)))
    (h : ∀ g ∈ generators, Skew g) :
    Subgroup.closure generators ≤ skewSubgroup Sh X :=
  (Subgroup.closure_le (skewSubgroup Sh X)).mpr h

/-- The full coordinate product acts without moving the shuffle. -/
def fiberPerm (f : Coordinates Sh X) : Perm (State Sh X) where
  toFun p := (p.1, fun j => f p.1 j (p.2 j))
  invFun p := (p.1, fun j => (f p.1 j).symm (p.2 j))
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

def fiberAction : Coordinates Sh X →* Perm (State Sh X) where
  toFun := fiberPerm
  map_one' := by ext p : 1; cases p; rfl
  map_mul' f k := by ext p : 1; cases p; rfl

theorem fiberAction_injective [∀ j, Nonempty (X j)] :
    Function.Injective (fiberAction : Coordinates Sh X →* Perm (State Sh X)) := by
  classical
  intro f k h
  funext s j
  apply Equiv.ext
  intro a
  let x : ∀ j, X j := Function.update (fun j => Classical.choice (inferInstance : Nonempty (X j))) j a
  have hx := congrArg (fun g : Perm (State Sh X) => (g (s, x)).2 j) h
  change f s j (x j) = k s j (x j) at hx
  simpa only [x, Function.update_self] using hx

/-- This is the full kernel ambient group, prior to restriction to BK. -/
def fiberKernel (Sh : Type*) (X : J → Type*) : Subgroup (Perm (State Sh X)) :=
  (fiberAction : Coordinates Sh X →* Perm (State Sh X)).range

theorem fiber_mem_iff [∀ j, Nonempty (X j)] (g : Perm (State Sh X)) :
    g ∈ fiberKernel Sh X ↔ Skew g ∧ ∀ p, (g p).1 = p.1 := by
  classical
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨⟨1, f, fun _ _ => rfl⟩, fun _ => rfl⟩
  · rintro ⟨⟨τ, f, hf⟩, hfix⟩
    refine ⟨f, ?_⟩
    ext p : 1
    rcases p with ⟨s, x⟩
    have hs : τ s = s := by
      simpa only [hf] using hfix (s, x)
    change (s, fun j => f s j (x j)) = g (s, x)
    rw [hf, hs]

/-- A canonical injective coordinate homomorphism for the shuffle-fixing
    subgroup. No order estimate on the total extension set is used. -/
noncomputable def kernelCoordinates [∀ j, Nonempty (X j)] :
    fiberKernel Sh X →* Coordinates Sh X :=
  (MonoidHom.ofInjective (fiberAction_injective (Sh := Sh) (X := X))).symm.toMonoidHom

theorem kernelCoordinates_injective [∀ j, Nonempty (X j)] :
    Function.Injective (kernelCoordinates : fiberKernel Sh X →* Coordinates Sh X) :=
  (MonoidHom.ofInjective (fiberAction_injective (Sh := Sh) (X := X))).symm.injective

#print axioms closure_le_skew
#print axioms fiber_mem_iff
#print axioms kernelCoordinates_injective
end Zigzag.Shuffle
```

### `ShuffleSectionBound.lean`

```lean
import ShuffleKernel
import SectionFree
import Mathlib.Data.Finite.Perm

namespace Zigzag.Shuffle
open Equiv

variable {Sh J : Type*} {X : J → Type*}
variable [∀ j, Nonempty (X j)]
variable {S B : Type*} [Group S] [Group B] [IsSimpleGroup S]
variable [Finite Sh] [Finite J]

/-- Abstract §1.2 bound. The shuffle quotient and the coordinate description
    are explicit hypotheses; applying this theorem to a poset requires proving
    those hypotheses via its actual shuffle/internal-extension bijection. -/
theorem sectionFree_of_shuffle_kernel
    (G : Subgroup (Perm (State Sh X))) (p : G →* B)
    (hskew : ∀ g : G, Skew g.val)
    (hfix : ∀ g : p.ker, ∀ u : State Sh X, (g.val.val u).1 = u.1)
    (hB : SectionFree S B) (hX : ∀ j, SectionFree S (Perm (X j))) :
    SectionFree S G := by
  apply sectionFree_extension p _ hB
  let j : p.ker →* fiberKernel Sh X :=
    { toFun := fun g => ⟨g.val.val, (fiber_mem_iff _).mpr ⟨hskew g.val, hfix g⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fiberKernel Sh X => z.val) hxy
  have hcoord : SectionFree S (Coordinates Sh X) :=
    sectionFree_pi (fun _ : Sh => ∀ j, Perm (X j))
      (fun _ => sectionFree_pi (fun j => Perm (X j)) hX)
  have hkernel : SectionFree S (fiberKernel Sh X) :=
    sectionFree_of_injective kernelCoordinates kernelCoordinates_injective hcoord
  exact sectionFree_of_injective j hj hkernel

/-- The quantitative form used in the ordinary proof: shuffle motion factors
    through the symmetric group on r positions; each component has e_j
    extensions. Importantly, |Sh|! is not used as the shuffle bound. -/
theorem sectionFree_of_shuffle_quotient [∀ j, Finite (X j)]
    (r : ℕ) (G : Subgroup (Perm (State Sh X))) (p : G →* B)
    (q : Perm (Fin r) →* B) (hq : Function.Surjective q)
    (hskew : ∀ g : G, Skew g.val)
    (hfix : ∀ g : p.ker, ∀ u : State Sh X, (g.val.val u).1 = u.1)
    (hr : r.factorial < Nat.card S)
    (he : ∀ j, (Nat.card (X j)).factorial < Nat.card S) : SectionFree S G := by
  apply sectionFree_of_shuffle_kernel G p hskew hfix
  · apply sectionFree_quotient q hq
    apply sectionFree_of_card_lt
    simpa only [Nat.card_perm, Nat.card_fin] using hr
  · intro j
    apply sectionFree_of_card_lt
    simpa only [Nat.card_perm] using he j

#print axioms sectionFree_of_shuffle_kernel
#print axioms sectionFree_of_shuffle_quotient
end Zigzag.Shuffle
```

### `PosetShufflePacket.lean`

```lean
import RemainingStatements
import ShuffleSectionBound

namespace Zigzag
open Equiv

instance componentLE_fintype {r k : ℕ} (R : Fin r → Fin r → Prop) [DecidableRel R]
    (c : Fin r → Fin k) (j : Fin k) : Fintype (ComponentLE R c j) := by
  unfold ComponentLE
  infer_instance

/-- Transport the actual BK group along an actual bijection, not an informal
    identification. Its source remains the literal position-to-vertex words. -/
def transportedBK {r k : ℕ} (R : Fin r → Fin r → Prop) [DecidableRel R]
    (c : Fin r → Fin k) {Sh : Type}
    (e : LinearExtensions R ≃ Shuffle.State Sh (ComponentLE R c)) :=
  (relationBK R).map e.permCongrHom.toMonoidHom

/-- Precisely the combinatorial data still needed to finish §1.2. Existence of
    this structure is NOT asserted. It contains a verified bijection and the
    shuffle quotient plus action properties, rather than a section-free bound.
    Empty components have singleton extension types; nonemptiness of each
    component extension set is required for faithful coordinate evaluation. -/
structure PosetShufflePacket {r k : ℕ} (R : Fin r → Fin r → Prop) [DecidableRel R]
    (c : Fin r → Fin k) where
  Sh : Type
  finiteSh : Finite Sh
  nonemptyComponents : ∀ j, Nonempty (ComponentLE R c j)
  encode : LinearExtensions R ≃ Shuffle.State Sh (ComponentLE R c)
  B : Type
  groupB : Group B
  projection : letI := groupB; transportedBK R c encode →* B
  positions : letI := groupB; Perm (Fin r) →* B
  positions_surjective : letI := groupB; Function.Surjective positions
  skew : ∀ g : transportedBK R c encode, Shuffle.Skew g.val
  fixes : letI := groupB
    ∀ g : projection.ker, ∀ u : Shuffle.State Sh (ComponentLE R c),
      (g.val.val u).1 = u.1

/-- Conditional §1.2, now stated for actual poset linear extensions. The only
    unproved bridge is the explicit packet argument; the section argument is
    completely discharged. -/
theorem leftover_sectionFree_of_packet {r k : ℕ} (R : Fin r → Fin r → Prop)
    [DecidableRel R] (c : Fin r → Fin k) (P : PosetShufflePacket R c)
    (S : Type) [Group S] [IsSimpleGroup S]
    (hr : r.factorial < Nat.card S)
    (he : ∀ j, (Nat.card (ComponentLE R c j)).factorial < Nat.card S) :
    SectionFree S (relationBK R) := by
  let := P.finiteSh
  let := P.nonemptyComponents
  let := P.groupB
  have htrans : SectionFree S (transportedBK R c P.encode) :=
    Shuffle.sectionFree_of_shuffle_quotient r _ P.projection P.positions
      P.positions_surjective P.skew P.fixes hr he
  exact sectionFree_of_injective
    (P.encode.permCongrHom.toMonoidHom.subgroupMap (relationBK R))
    (P.encode.permCongrHom.toMonoidHom.subgroupMap_injective (relationBK R)
      P.encode.permCongrHom.injective) htrans

/-- The exact missing theorem for §1.2. It is a proposition, not a proof. -/
def ShufflePacketsExist : Prop :=
  ∀ (r k : ℕ) (R : Fin r → Fin r → Prop) [DecidableRel R]
    [IsStrictOrder (Fin r) R] (c : Fin r → Fin k),
    (∀ a b, R a b → c a = c b) → Nonempty (PosetShufflePacket R c)

/-- All group theory for the residual bound is finished: packet existence
    alone suffices, without any subsequent diagonal or parity hypotheses. -/
theorem leftover_bound_of_packets (h : ShufflePacketsExist) : LeftoverSectionBound := by
  intro r k R _ _ c hc S _ _ _ hr he
  obtain ⟨P⟩ := h r k R c hc
  exact leftover_sectionFree_of_packet R c P S hr he

#print axioms leftover_sectionFree_of_packet
#print axioms leftover_bound_of_packets
end Zigzag
```

### `DiagonalIsolation.lean`

```lean
import SectionFree

namespace Zigzag
variable {S H B G : Type*} [Group S] [Group H] [Group B] [Group G]

/-- A simple quotient is independently available when the other action has no
    section isomorphic to it. This is the precise algebra behind isolating the
    diagonal alternating action in proof §1.1. -/
theorem isolate_simple_factor [IsSimpleGroup S]
    (p : H →* S) (hp : Function.Surjective p) (q : H →* B)
    (hB : SectionFree S B) : ∀ s, ∃ h, p h = s ∧ q h = 1 := by
  classical
  let N : Subgroup H := q.ker
  have hn : (N.map p).Normal := (inferInstance : N.Normal).map p hp
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · have hle : q.rangeRestrict.ker ≤ p.ker := by
      intro x hx
      have hx' : x ∈ N := by simpa only [MonoidHom.ker_rangeRestrict] using hx
      have hmem : p x ∈ N.map p := ⟨x, hx', rfl⟩
      rw [hbot] at hmem
      exact hmem
    let f : q.range →* S := q.rangeRestrict.liftOfSurjective
      q.rangeRestrict_surjective ⟨p, hle⟩
    have hf : Function.Surjective f := by
      intro s
      obtain ⟨x, rfl⟩ := hp s
      refine ⟨q.rangeRestrict x, ?_⟩
      exact q.rangeRestrict.liftOfRightInverse_comp_apply
        (Function.surjInv q.rangeRestrict_surjective)
        (Function.rightInverse_surjInv q.rangeRestrict_surjective) ⟨p, hle⟩ x
    exact False.elim ((sectionFree_subgroup hB q.range).no_surjective f hf)
  · intro s
    have hs : s ∈ N.map p := by rw [htop]; trivial
    obtain ⟨x, hx, he⟩ := hs
    exact ⟨x, he, hx⟩

/-- Restricting to the simple subgroup handles an S_d first projection with
    A_d as its simple subgroup; no normal-subgroup classification of S_d is
    needed. -/
theorem isolate_simple_subgroup (p : H →* G) (hp : Function.Surjective p)
    (q : H →* B) (A : Subgroup G) [IsSimpleGroup A]
    (hB : SectionFree A B) : ∀ a : A, ∃ h : H, p h = a.val ∧ q h = 1 := by
  intro a
  obtain ⟨h, hh, hq⟩ := isolate_simple_factor (p.subgroupComap A)
    (p.subgroupComap_surjective A hp) (q.comp (A.comap p).subtype) hB a
  exact ⟨h.val, congrArg (fun z : A => z.val) hh, hq⟩

#print axioms isolate_simple_factor
#print axioms isolate_simple_subgroup
end Zigzag
```

### `SingletonCommutator.lean`

```lean
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Zigzag
open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSimpArgs false

omit [DecidableEq α] in
private theorem perm_inv_cancel (f : Perm α) (y : α) : f (f⁻¹ y) = y :=
  f.apply_symm_apply y

omit [DecidableEq α] in
private theorem perm_cancel_inv (f : Perm α) (y : α) : f⁻¹ (f y) = y :=
  f.symm_apply_apply y

omit [DecidableEq α] in
private theorem inv_fixed (f : Perm α) {y : α} (h : f y = y) : f⁻¹ y = y := by
  apply f.injective
  simpa only [perm_inv_cancel] using h.symm

omit [DecidableEq α] in
private theorem inv_moved (f : Perm α) {y : α} (h : f y ≠ y) : f⁻¹ y ≠ y := by
  intro he
  apply h
  simpa only [perm_inv_cancel] using (congrArg f he).symm

/-- Two arbitrary permutations whose supports meet at precisely one moved
    point have a commutator which is exactly a single 3-cycle. No order-three
    assumption on the input permutations is needed. -/
theorem commutator_singleton (a b : Perm α) (x : α)
    (ha : a x ≠ x) (hb : b x ≠ x)
    (hint : ∀ y, a y ≠ y → b y ≠ y → y = x) :
    a * b * a⁻¹ * b⁻¹ = swap (a x) x * swap (a x) (b x) := by
  have abfix (y : α) (hay : a y ≠ y) (hy : y ≠ x) : b y = y := by
    by_contra hby
    exact hy (hint y hay hby)
  have bafix (y : α) (hby : b y ≠ y) (hy : y ≠ x) : a y = y := by
    by_contra hay
    exact hy (hint y hay hby)
  have hba : b (a x) = a x := abfix _ (a.injective.ne ha) ha
  have hab : a (b x) = b x := bafix _ (b.injective.ne hb) hb
  have habne : a x ≠ b x := by
    intro h
    apply ha
    have h' := hab
    rw [← h] at h'
    exact a.injective h'
  have hpreA : a (a⁻¹ x) ≠ a⁻¹ x := by
    rw [perm_inv_cancel]
    exact (inv_moved a ha).symm
  have hpreB : b (b⁻¹ x) ≠ b⁻¹ x := by
    rw [perm_inv_cancel]
    exact (inv_moved b hb).symm
  have hpreAB : b (a⁻¹ x) = a⁻¹ x := abfix _ hpreA (inv_moved a ha)
  have hpreBA : a (b⁻¹ x) = b⁻¹ x := bafix _ hpreB (inv_moved b hb)
  ext y
  by_cases hy : y = x
  · subst y
    simp only [Perm.mul_apply, inv_fixed a hpreBA, perm_inv_cancel]
    simp [swap_apply_def, ha, hb, habne, Ne.symm ha, Ne.symm hb, Ne.symm habne]
  by_cases hya : y = a x
  · subst y
    simp only [Perm.mul_apply, inv_fixed b hba, perm_cancel_inv]
    simp [swap_apply_def, hab, ha, hb, habne, Ne.symm ha, Ne.symm hb, Ne.symm habne]
  by_cases hyb : y = b x
  · subst y
    simp only [Perm.mul_apply, perm_cancel_inv, hpreAB, perm_inv_cancel]
    simp [swap_apply_def, ha, hb, habne, Ne.symm ha, Ne.symm hb, Ne.symm habne]
  have hright : (swap (a x) x * swap (a x) (b x)) y = y := by
    simp [Perm.mul_apply, swap_apply_def, hy, hya, hyb]
  rw [hright]
  simp only [Perm.mul_apply]
  by_cases hay : a y = y
  · by_cases hby : b y = y
    · simp only [inv_fixed b hby, inv_fixed a hay, hby, hay]
    · have hp : b (b⁻¹ y) ≠ b⁻¹ y := by
        rw [perm_inv_cancel]
        exact (inv_moved b hby).symm
      have hpx : b⁻¹ y ≠ x := by
        intro he
        apply hyb
        simpa only [perm_inv_cancel] using congrArg b he
      have hpfix := bafix _ hp hpx
      simp only [inv_fixed a hpfix, perm_inv_cancel, hay]
  · have hby : b y = y := abfix y hay hy
    have hp : a (a⁻¹ y) ≠ a⁻¹ y := by
      rw [perm_inv_cancel]
      exact (inv_moved a hay).symm
    have hpx : a⁻¹ y ≠ x := by
      intro he
      apply hya
      simpa only [perm_inv_cancel] using congrArg a he
    have hpfix := abfix _ hp hpx
    simp only [inv_fixed b hby, hpfix, perm_inv_cancel]

theorem commutator_isThreeCycle [Fintype α] (a b : Perm α) (x : α)
    (ha : a x ≠ x) (hb : b x ≠ x)
    (hint : ∀ y, a y ≠ y → b y ≠ y → y = x) :
    IsThreeCycle (a * b * a⁻¹ * b⁻¹) := by
  have hab : a x ≠ b x := by
    intro h
    have h1 : a (a x) ≠ a x := a.injective.ne ha
    have h2 : b (a x) ≠ a x := by rw [h]; exact b.injective.ne hb
    exact ha (hint _ h1 h2)
  rw [commutator_singleton a b x ha hb hint]
  exact isThreeCycle_swap_mul_swap_same ha hab hb.symm

#print axioms commutator_singleton
#print axioms commutator_isThreeCycle
end Zigzag
```

### `GroupSkeleton.lean`

```lean
import ZigzagDefinitions
import Mathlib.GroupTheory.GroupAction.Jordan

namespace Zigzag
open Equiv Equiv.Perm MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem full_of_alternating_and_odd (G : Subgroup (Perm α))
    (hA : alternatingGroup α ≤ G)
    (ho : ∃ g ∈ G, sign g = -1) : G = ⊤ := by
  obtain ⟨g, hg, hsign⟩ := ho
  apply top_unique
  intro p _
  rcases Int.units_eq_one_or (sign p) with hp | hp
  · exact hA (mem_alternatingGroup.mpr hp)
  · have he : p * g⁻¹ ∈ alternatingGroup α := by
      apply mem_alternatingGroup.mpr
      simp [map_mul, hp, hsign]
    have := G.mul_mem (hA he) hg
    simpa only [inv_mul_cancel_right] using this

theorem full_of_primitive_threeCycle_odd (G : Subgroup (Perm α))
    (hprimitive : IsPreprimitive G α)
    (hc : ∃ g ∈ G, IsThreeCycle g)
    (ho : ∃ g ∈ G, sign g = -1) : G = ⊤ := by
  obtain ⟨g, hg, hc⟩ := hc
  exact full_of_alternating_and_odd G
    (alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprimitive hc hg) ho

/-- The induction's genuine missing inputs are explicit hypotheses. -/
theorem even_zigzag_LE_symmetric_conditional
    (base0 : BKgroup 0 = ⊤) (base2 : BKgroup 2 = ⊤) (base4 : BKgroup 4 = ⊤)
    (alternating_step : ∀ n, Even n → 6 ≤ n → BKgroup (n - 2) = ⊤ →
      alternatingGroup (ZigzagLE n) ≤ BKgroup n)
    (odd_step : ∀ n, Even n → 6 ≤ n →
      ∃ g ∈ BKgroup n, sign g = -1) :
    ∀ n, Even n → BKgroup n = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h0 : n = 0
    · subst n; exact base0
    by_cases h2 : n = 2
    · subst n; exact base2
    by_cases h4 : n = 4
    · subst n; exact base4
    have h6 : 6 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
    have he : Even (n - 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k - 1, by omega⟩
    exact full_of_alternating_and_odd (BKgroup n)
      (alternating_step n hn h6 (ih (n - 2) (by omega) he)) (odd_step n hn h6)

#print axioms full_of_alternating_and_odd
#print axioms full_of_primitive_threeCycle_odd
#print axioms even_zigzag_LE_symmetric_conditional
end Zigzag
```

### `ConditionalEndpoint.lean`

```lean
import ZigzagBases
import SourceBridge
import PosetShufflePacket
import DiagonalIsolation
import SingletonCommutator
import GroupSkeleton

namespace Zigzag
open Equiv Equiv.Perm MulAction

/-- The exact target follows once the two stated uniform fence-specific steps
    are supplied. This declaration does not assert either missing step. -/
theorem even_zigzag_LE_symmetric_from_steps
    (hA : AlternatingStep) (hO : OddStep) (n : ℕ) (hn : Even n) : BKgroup n = ⊤ := by
  apply even_zigzag_LE_symmetric_conditional zero_symmetric two_symmetric four_symmetric hA _ n hn
  intro m hm hm6
  have h : 2 < m := by omega
  exact ⟨bk m 1 h, bk_mem m 1 h, hO m h hm (by omega)⟩

/-- A general interface for the geometric construction: a verified singleton
    overlap, a primitive action, and an odd element suffice. Primitivity is an
    essential hypothesis; mere transitivity has not been substituted for it. -/
theorem full_of_singleton_overlap_and_primitive {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) (hprimitive : IsPreprimitive G α)
    (a b : Perm α) (haG : a ∈ G) (hbG : b ∈ G) (x : α)
    (ha : a x ≠ x) (hb : b x ≠ x)
    (hint : ∀ y, a y ≠ y → b y ≠ y → y = x)
    (hodd : ∃ g ∈ G, sign g = -1) : G = ⊤ := by
  apply full_of_primitive_threeCycle_odd G hprimitive _ hodd
  refine ⟨a * b * a⁻¹ * b⁻¹, ?_, commutator_isThreeCycle a b x ha hb hint⟩
  exact G.mul_mem (G.mul_mem (G.mul_mem haG hbG) (G.inv_mem haG)) (G.inv_mem hbG)

#print axioms even_zigzag_LE_symmetric_from_steps
#print axioms full_of_singleton_overlap_and_primitive
#eval Lean.versionString
end Zigzag
```

### `Audit.lean`

```lean
import ConditionalEndpoint

set_option pp.universes false

#check Zigzag.zigLt_strictOrder
#check Zigzag.rawSwap_isLE_iff
#check Zigzag.move_apply
#check Zigzag.move_involutive
#check Zigzag.bk_mem
#check Zigzag.sourceLabelBridge
#check Zigzag.bk_source_labels
#check Zigzag.card_zigzagLE_four
#check Zigzag.card_zigzagLE_six
#check Zigzag.zero_symmetric
#check Zigzag.two_symmetric
#check Zigzag.four_symmetric
#check Zigzag.sectionFree_of_card_lt
#check Zigzag.sectionFree_of_injective
#check Zigzag.sectionFree_subgroup
#check Zigzag.sectionFree_quotient
#check Zigzag.sectionFree_extension
#check Zigzag.sectionFree_prod
#check Zigzag.sectionFree_pi
#check Zigzag.Shuffle.closure_le_skew
#check Zigzag.Shuffle.fiber_mem_iff
#check Zigzag.Shuffle.kernelCoordinates_injective
#check Zigzag.Shuffle.sectionFree_of_shuffle_quotient
#check Zigzag.leftover_sectionFree_of_packet
#check Zigzag.leftover_bound_of_packets
#check Zigzag.isolate_simple_subgroup
#check Zigzag.commutator_singleton
#check Zigzag.commutator_isThreeCycle
#check Zigzag.full_of_alternating_and_odd
#check Zigzag.full_of_primitive_threeCycle_odd
#check Zigzag.even_zigzag_LE_symmetric_from_steps
#check Zigzag.full_of_singleton_overlap_and_primitive

#print axioms Zigzag.even_zigzag_LE_symmetric_from_steps
#print axioms Zigzag.four_symmetric
#print axioms Zigzag.leftover_bound_of_packets
#print axioms Zigzag.full_of_singleton_overlap_and_primitive
```

### `FenceGeometry.lean`

```lean
import SourceBridge
import RemainingStatements

namespace Zigzag

/-- Numerical interval condition for the vertices remaining after two deletions.
This is not an assertion about a graph until the connectivity bridge is proved. -/
def ResidualInterval (n : ℕ) (a b : Fin n) : Prop :=
  ∀ x y z : Fin n, x ≠ a → x ≠ b → y ≠ a → y ≠ b →
    x ≤ z → z ≤ y → z ≠ a ∧ z ≠ b

/-- Every extension starts at a minimal vertex, in the source's orientation. -/
theorem first_vertex_even {n : ℕ} (hn : 0 < n) (w : ZigzagLE n) :
    (w.val ⟨0, hn⟩).val % 2 = 0 := by
  apply (minimal_iff_even n _).mp
  intro b hab
  have h := w.property _ _ hab
  have he : w.val.symm (w.val ⟨0, hn⟩) = ⟨0, hn⟩ := w.val.symm_apply_apply _
  rw [he] at h
  change (w.val.symm b).val < 0 at h
  omega

/-- In even order every extension ends at an odd Lean vertex, a source maximum. -/
theorem last_vertex_odd {n : ℕ} (hn : Even n) (hpos : 0 < n) (w : ZigzagLE n) :
    (w.val ⟨n - 1, by omega⟩).val % 2 = 1 := by
  let a := w.val ⟨n - 1, by omega⟩
  have ha : a.val < n := a.isLt
  have hnmod : n % 2 = 0 := by obtain ⟨m, hm⟩ := hn; omega
  by_contra h
  have heven : a.val % 2 = 0 := by omega
  have hb : a.val + 1 < n := by omega
  let b : Fin n := ⟨a.val + 1, hb⟩
  have hab : zigLt n a b := ⟨heven, Or.inl rfl⟩
  have hh := w.property a b hab
  have he : w.val.symm a = ⟨n - 1, by omega⟩ := w.val.symm_apply_apply _
  rw [he] at hh
  have := (w.val.symm b).isLt
  change n - 1 < (w.val.symm b).val at hh
  omega

/-- The A-residue shift by two preserves the literal fence relation. -/
theorem zigLt_shift_two (r : ℕ) (a b : Fin r) :
    zigLt (r + 2) ⟨a.val + 2, by omega⟩ ⟨b.val + 2, by omega⟩ ↔ zigLt r a b := by
  simp only [zigLt]
  omega

/-- The C-residue inclusion preserves the literal fence relation. -/
theorem zigLt_include_two (r : ℕ) (a b : Fin r) :
    zigLt (r + 2) ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ ↔ zigLt r a b := Iff.rfl

/-- The B-residue reflection (source j ↦ n-j) preserves orientation when r is even. -/
theorem zigLt_reflect_interior (r : ℕ) (hr : Even r) (a b : Fin r) :
    zigLt (r + 2) ⟨r - a.val, by omega⟩ ⟨r - b.val, by omega⟩ ↔ zigLt r a b := by
  have hrmod : r % 2 = 0 := by obtain ⟨m, hm⟩ := hr; omega
  simp only [zigLt]
  omega

/-- The only interval residues compatible with a minimal first vertex and a
maximal last vertex are precisely the three endpoint pairs in proof (4).
Graph-connectivity and extension-fiber equivalences remain separate obligations. -/
theorem residual_interval_endpoints {n : ℕ} (hn : 6 ≤ n) (heven : Even n) (a b : Fin n)
    (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) :
    ResidualInterval n a b ↔
      (a.val = 0 ∧ b.val = 1) ∨ (a.val = 0 ∧ b.val = n - 1) ∨
        (a.val = n - 2 ∧ b.val = n - 1) := by
  have hnmod : n % 2 = 0 := by obtain ⟨m, hm⟩ := heven; omega
  constructor
  · intro h
    have hne (x y : Fin n) (hv : x.val ≠ y.val) : x ≠ y :=
      fun he => hv (congrArg Fin.val he)
    by_cases ha0 : a.val = 0
    · by_cases hbtop : b.val = n - 1
      · exact Or.inr (Or.inl ⟨ha0, hbtop⟩)
      · by_cases hb1 : b.val = 1
        · exact Or.inl ⟨ha0, hb1⟩
        · have hh := h ⟨1, by omega⟩ ⟨n - 1, by omega⟩ b
            (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
            (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
            (by change 1 ≤ b.val; omega) (by change b.val ≤ n - 1; omega)
          exact False.elim (hh.2 rfl)
    · by_cases hbtop : b.val = n - 1
      · by_cases hanext : a.val = n - 2
        · exact Or.inr (Or.inr ⟨hanext, hbtop⟩)
        · have hh := h ⟨0, by omega⟩ ⟨n - 2, by omega⟩ a
            (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
            (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
            (by change 0 ≤ a.val; omega) (by change a.val ≤ n - 2; omega)
          exact False.elim (hh.1 rfl)
      · have hh := h ⟨0, by omega⟩ ⟨n - 1, by omega⟩ a
          (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
          (hne _ _ (by dsimp; omega)) (hne _ _ (by dsimp; omega))
          (by change 0 ≤ a.val; omega) (by change a.val ≤ n - 1; omega)
        exact False.elim (hh.1 rfl)
  · intro hab x y z hxa hxb hya hyb hxz hzy
    have hxa' : x.val ≠ a.val := fun he => hxa (Fin.ext he)
    have hxb' : x.val ≠ b.val := fun he => hxb (Fin.ext he)
    have hya' : y.val ≠ a.val := fun he => hya (Fin.ext he)
    have hyb' : y.val ≠ b.val := fun he => hyb (Fin.ext he)
    simp only [Fin.le_def] at hxz hzy
    constructor <;> intro he <;> have hz := congrArg Fin.val he <;> omega

#print axioms first_vertex_even
#print axioms last_vertex_odd
#print axioms zigLt_shift_two
#print axioms zigLt_reflect_interior
#print axioms residual_interval_endpoints
end Zigzag
```

### `FenceEndpointA.lean`

```lean
import FenceGeometry
import Mathlib.Logic.Equiv.Fin.Basic

namespace Zigzag
open Equiv

/-- Split the first position, last position, and middle positions, in that order. -/
def splitPositions (r : ℕ) : Fin (r + 2) ≃ Option (Option (Fin r)) :=
  (finSuccEquiv (r + 1)).trans (Equiv.optionCongr finSuccEquivLast)

/-- Split source vertices 1, 2, and the shifted residual fence. -/
def splitAVertices (r : ℕ) : Fin (r + 2) ≃ Option (Option (Fin r)) :=
  (finSuccEquiv (r + 1)).trans (Equiv.optionCongr (finSuccEquiv r))

/-- Source A(w)=(1,w+2,2), as an actual permutation on positions and vertices. -/
def padA {r : ℕ} (w : Perm (Fin r)) : Perm (Fin (r + 2)) :=
  (splitPositions r).trans ((Equiv.optionCongr (Equiv.optionCongr w)).trans
    (splitAVertices r).symm)

@[simp] theorem padA_first {r : ℕ} (w : Perm (Fin r)) : padA w 0 = 0 := by
  simp [padA, splitPositions, splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem padA_last {r : ℕ} (w : Perm (Fin r)) :
    padA w (Fin.last (r + 1)) = 1 := by
  simp [padA, splitPositions, splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem padA_middle {r : ℕ} (w : Perm (Fin r)) (a : Fin r) :
    padA w a.castSucc.succ = (w a).succ.succ := by
  simp [padA, splitPositions, splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem padA_symm_first {r : ℕ} (w : Perm (Fin r)) : (padA w).symm 0 = 0 :=
  (padA w).symm_apply_eq.mpr (padA_first w).symm

@[simp] theorem padA_symm_last {r : ℕ} (w : Perm (Fin r)) :
    (padA w).symm 1 = Fin.last (r + 1) :=
  (padA w).symm_apply_eq.mpr (padA_last w).symm

@[simp] theorem padA_symm_middle {r : ℕ} (w : Perm (Fin r)) (a : Fin r) :
    (padA w).symm a.succ.succ = (w.symm a).castSucc.succ := by
  apply (padA w).symm_apply_eq.mpr
  simp

/-- Padding preserves the exact order condition. -/
theorem padA_isLE {r : ℕ} (w : ZigzagLE r) : IsLE (zigLt (r + 2)) (padA w.val) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact False.elim (zigLt_irrefl _ _ hab)
    | succ b =>
      induction b using Fin.cases with
      | zero => simp [Fin.lt_def]
      | succ b => simp [Fin.lt_def]
  | succ a =>
    induction a using Fin.cases with
    | zero =>
      have hpar := hab.1
      change 1 % 2 = 0 at hpar
      omega
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        have hadj := hab.2
        simp only [Fin.val_zero, Fin.val_succ] at hadj
        omega
      | succ b =>
        induction b using Fin.cases with
        | zero =>
          change (padA w.val).symm a.succ.succ < (padA w.val).symm 1
          rw [padA_symm_last, padA_symm_middle]
          change (w.val.symm a).val + 1 < r + 1
          have := (w.val.symm a).isLt
          omega
        | succ b =>
          have hsmall : zigLt r a b := (zigLt_shift_two r a b).mp hab
          have hh := w.property a b hsmall
          simpa only [padA_symm_middle, Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff] using hh

def endpointA {r : ℕ} (w : ZigzagLE r) : ZigzagLE (r + 2) :=
  ⟨padA w.val, padA_isLE w⟩

theorem endpointA_injective (r : ℕ) : Function.Injective (@endpointA r) := by
  intro w v he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have hh := congrArg (fun u : ZigzagLE (r + 2) => u.val a.castSucc.succ) he
  simpa only [endpointA, padA_middle, Fin.succ_inj] using hh

#print axioms endpointA
#print axioms endpointA_injective
end Zigzag
```

### `EndpointFrames.lean`

```lean
import FenceEndpointA
import Mathlib.Logic.Equiv.Option

namespace Zigzag
open Equiv

/-- A literal residual-fence coordinate system, with a minimal first vertex
and a maximal last vertex. The relation field is an equivalence, not an assumption
that the padded words happen to be extensions. -/
structure EndpointFrame (r : ℕ) where
  vertices : Fin (r + 2) ≃ Option (Option (Fin r))
  first_min : ∀ a, ¬ zigLt (r + 2) a (vertices.symm none)
  last_max : ∀ b, ¬ zigLt (r + 2) (vertices.symm (some none)) b
  middle_rel : ∀ a b : Fin r,
    zigLt (r + 2) (vertices.symm (some (some a)))
      (vertices.symm (some (some b))) ↔ zigLt r a b

namespace EndpointFrame
variable {r : ℕ} (F : EndpointFrame r)

def pad (w : Perm (Fin r)) : Perm (Fin (r + 2)) :=
  (splitPositions r).trans ((optionCongr (optionCongr w)).trans F.vertices.symm)

@[simp] theorem pad_first (w : Perm (Fin r)) :
    F.pad w 0 = F.vertices.symm none := by
  simp [pad, splitPositions]

@[simp] theorem pad_last (w : Perm (Fin r)) :
    F.pad w (Fin.last (r + 1)) = F.vertices.symm (some none) := by
  simp [pad, splitPositions]

@[simp] theorem pad_middle (w : Perm (Fin r)) (a : Fin r) :
    F.pad w a.castSucc.succ = F.vertices.symm (some (some (w a))) := by
  simp [pad, splitPositions]

@[simp] theorem pad_symm_first (w : Perm (Fin r)) :
    (F.pad w).symm (F.vertices.symm none) = 0 :=
  (F.pad w).symm_apply_eq.mpr (F.pad_first w).symm

@[simp] theorem pad_symm_last (w : Perm (Fin r)) :
    (F.pad w).symm (F.vertices.symm (some none)) = Fin.last (r + 1) :=
  (F.pad w).symm_apply_eq.mpr (F.pad_last w).symm

@[simp] theorem pad_symm_middle (w : Perm (Fin r)) (a : Fin r) :
    (F.pad w).symm (F.vertices.symm (some (some a))) = (w.symm a).castSucc.succ := by
  apply (F.pad w).symm_apply_eq.mpr
  simp

theorem pad_isLE_iff (w : Perm (Fin r)) :
    IsLE (zigLt (r + 2)) (F.pad w) ↔ IsLE (zigLt r) w := by
  constructor
  · intro h a b hab
    have hh := h _ _ ((F.middle_rel a b).mpr hab)
    simpa only [pad_symm_middle, Fin.succ_lt_succ_iff,
      Fin.castSucc_lt_castSucc_iff] using hh
  · intro h a b hab
    obtain ⟨x, rfl⟩ := F.vertices.symm.surjective a
    obtain ⟨y, rfl⟩ := F.vertices.symm.surjective b
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (F.first_min _ hab)
      | some y =>
        cases y with
        | none => simp [Fin.lt_def]
        | some y => simp [Fin.lt_def]
    | some x =>
      cases x with
      | none => exact False.elim (F.last_max _ hab)
      | some x =>
        cases y with
        | none => exact False.elim (F.first_min _ hab)
        | some y =>
          cases y with
          | none =>
            simp only [pad_symm_middle, pad_symm_last]
            change (w.symm x).val + 1 < r + 1
            have := (w.symm x).isLt
            omega
          | some y =>
            have hh := h _ _ ((F.middle_rel x y).mp hab)
            simpa only [pad_symm_middle, Fin.succ_lt_succ_iff,
              Fin.castSucc_lt_castSucc_iff] using hh

def extension (w : ZigzagLE r) : ZigzagLE (r + 2) :=
  ⟨F.pad w.val, (F.pad_isLE_iff w.val).mpr w.property⟩

def Fiber := {w : ZigzagLE (r + 2) //
  w.val 0 = F.vertices.symm none ∧
  w.val (Fin.last (r + 1)) = F.vertices.symm (some none)}

theorem pad_injective : Function.Injective F.pad := by
  intro w v h
  apply Equiv.ext
  intro a
  have hh := congrArg (fun e : Perm (Fin (r + 2)) => F.vertices (e a.castSucc.succ)) h
  simpa only [pad_middle, Equiv.apply_symm_apply, Option.some.injEq] using hh

theorem extension_injective : Function.Injective F.extension := by
  intro w v h
  exact Subtype.ext (F.pad_injective (congrArg Subtype.val h))

/-- Removing a fixed none recovers the entire permutation, not merely its values
on a selected subset. -/
theorem optionCongr_removeNone_fixed {α : Type*} (e : Perm (Option α))
    (h : e none = none) : optionCongr (removeNone e) = e := by
  apply Equiv.ext
  intro x
  cases x with
  | none => simpa using h.symm
  | some x =>
    change some (removeNone e x) = e (some x)
    apply removeNone_some
    cases hx : e (some x) with
    | none =>
      have hh := e.injective (hx.trans h.symm)
      cases hh
    | some y => exact ⟨y, rfl⟩

/-- Every word in the full specified-endpoint fiber is a padded smaller word. -/
theorem exists_pad (w : F.Fiber) : ∃ v : ZigzagLE r, F.extension v = w.val := by
  let e : Perm (Option (Option (Fin r))) :=
    (splitPositions r).symm.trans (w.val.val.trans F.vertices)
  have he0 : e none = none := by
    change F.vertices (w.val.val ((splitPositions r).symm none)) = none
    have hp : (splitPositions r).symm none = 0 := by simp [splitPositions, ← Equiv.optionCongr_symm]
    rw [hp, w.property.1]
    simp
  have he1 : e (some none) = some none := by
    change F.vertices (w.val.val ((splitPositions r).symm (some none))) = some none
    have hp : (splitPositions r).symm (some none) = Fin.last (r + 1) := by
      simp [splitPositions, ← Equiv.optionCongr_symm]
    rw [hp, w.property.2]
    simp
  have hrec := optionCongr_removeNone_fixed e he0
  have hr0 : removeNone e none = none := by
    apply Option.some_injective
    have hh := Equiv.congr_fun hrec (some none)
    simpa only [optionCongr_apply, Option.map_none, Option.map_some, he1] using hh
  let v := removeNone (removeNone e)
  have hr : optionCongr (optionCongr v) = e := by
    rw [show optionCongr v = removeNone e from
      optionCongr_removeNone_fixed (removeNone e) hr0]
    exact hrec
  have hpad : F.pad v = w.val.val := by
    apply Equiv.ext
    intro a
    have hh := Equiv.congr_fun hr (splitPositions r a)
    apply F.vertices.injective
    simpa only [pad, Equiv.trans_apply, Equiv.apply_symm_apply,
      e, Equiv.symm_apply_apply] using hh
  have hv : IsLE (zigLt r) v := (F.pad_isLE_iff v).mp (hpad ▸ w.val.property)
  exact ⟨⟨v, hv⟩, Subtype.ext hpad⟩

noncomputable def fiberEquiv : ZigzagLE r ≃ F.Fiber :=
  Equiv.ofBijective
    (fun w => ⟨F.extension w, F.pad_first w.val, F.pad_last w.val⟩)
    ⟨fun _ _ h => F.extension_injective (congrArg Subtype.val h),
      fun w => by obtain ⟨v, hv⟩ := F.exists_pad w; exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem fiberEquiv_val (w : ZigzagLE r) :
    (F.fiberEquiv w).val = F.extension w := rfl

#print axioms pad_isLE_iff
#print axioms exists_pad
#print axioms fiberEquiv
end EndpointFrame
end Zigzag
```

### `ResidualFrames.lean`

```lean
import EndpointFrames
import Mathlib.Logic.Equiv.Option

namespace Zigzag
open Equiv

/-- Arbitrary endpoint coordinates, including disconnected residues. The residual
relation is pulled back from the literal fence, without a connectivity assumption. -/
structure ResidualFrame (r : ℕ) where
  vertices : Fin (r + 2) ≃ Option (Option (Fin r))
  first_min : ∀ a, ¬ zigLt (r + 2) a (vertices.symm none)
  last_max : ∀ b, ¬ zigLt (r + 2) (vertices.symm (some none)) b

namespace ResidualFrame
variable {r : ℕ} (F : ResidualFrame r)

def relation (a b : Fin r) : Prop :=
  zigLt (r + 2) (F.vertices.symm (some (some a)))
    (F.vertices.symm (some (some b)))

instance : DecidableRel F.relation := fun _ _ => inferInstanceAs (Decidable (zigLt _ _ _))

instance : IsStrictOrder (Fin r) F.relation where
  irrefl _ := zigLt_irrefl _ _
  trans _ _ _ hab hbc := zigLt_trans _ _ _ _ hab hbc


def pad (w : Perm (Fin r)) : Perm (Fin (r + 2)) :=
  (splitPositions r).trans ((optionCongr (optionCongr w)).trans F.vertices.symm)

@[simp] theorem pad_first (w : Perm (Fin r)) :
    F.pad w 0 = F.vertices.symm none := by
  simp [pad, splitPositions]

@[simp] theorem pad_last (w : Perm (Fin r)) :
    F.pad w (Fin.last (r + 1)) = F.vertices.symm (some none) := by
  simp [pad, splitPositions]

@[simp] theorem pad_middle (w : Perm (Fin r)) (a : Fin r) :
    F.pad w a.castSucc.succ = F.vertices.symm (some (some (w a))) := by
  simp [pad, splitPositions]

@[simp] theorem pad_symm_first (w : Perm (Fin r)) :
    (F.pad w).symm (F.vertices.symm none) = 0 :=
  (F.pad w).symm_apply_eq.mpr (F.pad_first w).symm

@[simp] theorem pad_symm_last (w : Perm (Fin r)) :
    (F.pad w).symm (F.vertices.symm (some none)) = Fin.last (r + 1) :=
  (F.pad w).symm_apply_eq.mpr (F.pad_last w).symm

@[simp] theorem pad_symm_middle (w : Perm (Fin r)) (a : Fin r) :
    (F.pad w).symm (F.vertices.symm (some (some a))) = (w.symm a).castSucc.succ := by
  apply (F.pad w).symm_apply_eq.mpr
  simp

theorem pad_isLE_iff (w : Perm (Fin r)) :
    IsLE (zigLt (r + 2)) (F.pad w) ↔ IsLE F.relation w := by
  constructor
  · intro h a b hab
    have hh := h _ _ hab
    simpa only [pad_symm_middle, Fin.succ_lt_succ_iff,
      Fin.castSucc_lt_castSucc_iff] using hh
  · intro h a b hab
    obtain ⟨x, rfl⟩ := F.vertices.symm.surjective a
    obtain ⟨y, rfl⟩ := F.vertices.symm.surjective b
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (F.first_min _ hab)
      | some y =>
        cases y with
        | none => simp [Fin.lt_def]
        | some y => simp [Fin.lt_def]
    | some x =>
      cases x with
      | none => exact False.elim (F.last_max _ hab)
      | some x =>
        cases y with
        | none => exact False.elim (F.first_min _ hab)
        | some y =>
          cases y with
          | none =>
            simp only [pad_symm_middle, pad_symm_last]
            change (w.symm x).val + 1 < r + 1
            have := (w.symm x).isLt
            omega
          | some y =>
            have hh := h _ _ hab
            simpa only [pad_symm_middle, Fin.succ_lt_succ_iff,
              Fin.castSucc_lt_castSucc_iff] using hh

def extension (w : LinearExtensions F.relation) : ZigzagLE (r + 2) :=
  ⟨F.pad w.val, (F.pad_isLE_iff w.val).mpr w.property⟩

def Fiber := {w : ZigzagLE (r + 2) //
  w.val 0 = F.vertices.symm none ∧
  w.val (Fin.last (r + 1)) = F.vertices.symm (some none)}

theorem pad_injective : Function.Injective F.pad := by
  intro w v h
  apply Equiv.ext
  intro a
  have hh := congrArg (fun e : Perm (Fin (r + 2)) => F.vertices (e a.castSucc.succ)) h
  simpa only [pad_middle, Equiv.apply_symm_apply, Option.some.injEq] using hh

theorem extension_injective : Function.Injective F.extension := by
  intro w v h
  exact Subtype.ext (F.pad_injective (congrArg Subtype.val h))

/-- Every word in the full specified-endpoint fiber is a padded smaller word. -/
theorem exists_pad (w : F.Fiber) : ∃ v : LinearExtensions F.relation, F.extension v = w.val := by
  let e : Perm (Option (Option (Fin r))) :=
    (splitPositions r).symm.trans (w.val.val.trans F.vertices)
  have he0 : e none = none := by
    change F.vertices (w.val.val ((splitPositions r).symm none)) = none
    have hp : (splitPositions r).symm none = 0 := by simp [splitPositions, ← Equiv.optionCongr_symm]
    rw [hp, w.property.1]
    simp
  have he1 : e (some none) = some none := by
    change F.vertices (w.val.val ((splitPositions r).symm (some none))) = some none
    have hp : (splitPositions r).symm (some none) = Fin.last (r + 1) := by
      simp [splitPositions, ← Equiv.optionCongr_symm]
    rw [hp, w.property.2]
    simp
  have hrec := EndpointFrame.optionCongr_removeNone_fixed e he0
  have hr0 : removeNone e none = none := by
    apply Option.some_injective
    have hh := Equiv.congr_fun hrec (some none)
    simpa only [optionCongr_apply, Option.map_none, Option.map_some, he1] using hh
  let v := removeNone (removeNone e)
  have hr : optionCongr (optionCongr v) = e := by
    rw [show optionCongr v = removeNone e from
      EndpointFrame.optionCongr_removeNone_fixed (removeNone e) hr0]
    exact hrec
  have hpad : F.pad v = w.val.val := by
    apply Equiv.ext
    intro a
    have hh := Equiv.congr_fun hr (splitPositions r a)
    apply F.vertices.injective
    simpa only [pad, Equiv.trans_apply, Equiv.apply_symm_apply,
      e, Equiv.symm_apply_apply] using hh
  have hv : IsLE F.relation v := (F.pad_isLE_iff v).mp (hpad ▸ w.val.property)
  exact ⟨⟨v, hv⟩, Subtype.ext hpad⟩

noncomputable def fiberEquiv : LinearExtensions F.relation ≃ F.Fiber :=
  Equiv.ofBijective
    (fun w => ⟨F.extension w, F.pad_first w.val, F.pad_last w.val⟩)
    ⟨fun _ _ h => F.extension_injective (congrArg Subtype.val h),
      fun w => by obtain ⟨v, hv⟩ := F.exists_pad w; exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem fiberEquiv_val (w : LinearExtensions F.relation) :
    (F.fiberEquiv w).val = F.extension w := rfl

#print axioms pad_isLE_iff
#print axioms exists_pad
#print axioms fiberEquiv
end ResidualFrame
end Zigzag
```

### `FenceEndpointAction.lean`

```lean
import FenceEndpointA

namespace Zigzag
open Equiv

/-- Internal adjacent positions shift by one under endpoint padding. -/
theorem adjacentSwap_middle {r : ℕ} (i : ℕ) (hi : i + 1 < r) (a : Fin r) :
    adjacentSwap (i + 1) (by omega : i + 1 + 1 < r + 2) a.castSucc.succ =
      (adjacentSwap i hi a).castSucc.succ := by
  have hleft : leftPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (leftPos i hi).castSucc.succ := by ext; simp [leftPos]
  have hright : rightPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (rightPos i hi).castSucc.succ := by ext; simp [rightPos]
  simp only [adjacentSwap, hleft, hright, Equiv.swap_apply_def,
    Fin.succ_inj, Fin.castSucc_inj]
  split_ifs <;> rfl

theorem rawSwap_padA {r : ℕ} (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    rawSwap (i + 1) (by omega : i + 1 + 1 < r + 2) (padA w) =
      padA (rawSwap i hi w) := by
  apply Equiv.ext
  intro a
  change padA w (adjacentSwap (i + 1) (by omega : i + 1 + 1 < r + 2) a) = padA (rawSwap i hi w) a
  induction a using Fin.cases with
  | zero =>
    have he : adjacentSwap (i + 1) (by omega : i + 1 + 1 < r + 2) 0 = 0 := by
      simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos, Fin.ext_iff]
    simp [he]
  | succ a =>
    induction a using Fin.lastCases with
    | last =>
      change padA w (adjacentSwap (i + 1) _ (Fin.last (r + 1))) = _
      have he : adjacentSwap (i + 1) (by omega : i + 1 + 1 < r + 2)
          (Fin.last (r + 1)) = Fin.last (r + 1) := by
        have hl : Fin.last (r + 1) ≠ leftPos (i + 1) (by omega : i + 1 + 1 < r + 2) := by
          intro he
          have hh := congrArg Fin.val he
          change r + 1 = i + 1 at hh
          omega
        have hr : Fin.last (r + 1) ≠ rightPos (i + 1) (by omega : i + 1 + 1 < r + 2) := by
          intro he
          have hh := congrArg Fin.val he
          change r + 1 = i + 1 + 1 at hh
          omega
        simp [adjacentSwap, Equiv.swap_apply_def, hl, hr]
      simp [he]
    | cast a =>
      rw [adjacentSwap_middle, padA_middle, padA_middle]
      rfl

/-- The source incomparability test agrees under the literal A embedding. -/
theorem incomparable_padA {r : ℕ} (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    incomparable (zigLt (r + 2)) (i + 1) (by omega : i + 1 + 1 < r + 2) (padA w) ↔
      incomparable (zigLt r) i hi w := by
  have hl : leftPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (leftPos i hi).castSucc.succ := by ext; simp [leftPos]
  have hr : rightPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (rightPos i hi).castSucc.succ := by ext; simp [rightPos]
  simp only [incomparable, hl, hr, padA_middle]
  exact and_congr (not_congr (zigLt_shift_two r _ _)) (not_congr (zigLt_shift_two r _ _))

/-- Internal generators on the A-fiber act by exactly the smaller fence's BK
involutions. This is an equality of literal extension words. -/
theorem bk_endpointA {r : ℕ} (i : ℕ) (hi : i + 1 < r) (w : ZigzagLE r) :
    bk (r + 2) (i + 1) (by omega) (endpointA w) = endpointA (bk r i hi w) := by
  apply Subtype.ext
  change (move (zigLt (r + 2)) (i + 1) _ (endpointA w)).val = padA ((bk r i hi w).val)
  rw [move_apply]
  change (if incomparable (zigLt (r + 2)) (i + 1) _ (padA w.val) then _ else _) = _
  rw [show (bk r i hi w).val = _ from move_apply (zigLt r) i hi w]
  by_cases h : incomparable (zigLt r) i hi w.val
  · simp only [(incomparable_padA i hi w.val).mpr h, ite_true, h]
    exact rawSwap_padA i hi w.val
  · simp only [(incomparable_padA i hi w.val).not.mpr h, ite_false, h]
    rfl

#print axioms bk_endpointA
end Zigzag
```

### `ResidualFrameAction.lean`

```lean
import ResidualFrames
import FenceEndpointAction

namespace Zigzag
open Equiv
namespace ResidualFrame
variable {r : ℕ} (F : ResidualFrame r)

theorem pad_factor (w : Perm (Fin r)) :
    F.pad w = (padA w).trans ((splitAVertices r).trans F.vertices.symm) := by
  ext a
  simp [pad, padA]

theorem rawSwap_pad (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    rawSwap (i + 1) (by omega : i + 1 + 1 < r + 2) (F.pad w) =
      F.pad (rawSwap i hi w) := by
  rw [F.pad_factor w, F.pad_factor (rawSwap i hi w)]
  have hh := congrArg (fun e : Perm (Fin (r + 2)) =>
    e.trans ((splitAVertices r).trans F.vertices.symm)) (rawSwap_padA i hi w)
  simpa only [rawSwap, Equiv.trans_assoc] using hh

theorem incomparable_pad (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    incomparable (zigLt (r + 2)) (i + 1) (by omega : i + 1 + 1 < r + 2) (F.pad w) ↔
      incomparable F.relation i hi w := by
  have hl : leftPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (leftPos i hi).castSucc.succ := by ext; simp [leftPos]
  have hr : rightPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (rightPos i hi).castSucc.succ := by ext; simp [rightPos]
  simp only [incomparable, hl, hr, pad_middle]
  rfl

theorem bk_extension (i : ℕ) (hi : i + 1 < r) (w : LinearExtensions F.relation) :
    bk (r + 2) (i + 1) (by omega) (F.extension w) = F.extension (move F.relation i hi w) := by
  apply Subtype.ext
  change (move (zigLt (r + 2)) (i + 1) _ (F.extension w)).val = F.pad ((move F.relation i hi w).val)
  rw [move_apply]
  change (if incomparable (zigLt (r + 2)) (i + 1) _ (F.pad w.val) then _ else _) = _
  rw [show (move F.relation i hi w).val = _ from move_apply F.relation i hi w]
  by_cases h : incomparable F.relation i hi w.val
  · simp only [(F.incomparable_pad i hi w.val).mpr h, ite_true, h]
    exact F.rawSwap_pad i hi w.val
  · simp only [(F.incomparable_pad i hi w.val).not.mpr h, ite_false, h]
    rfl

#print axioms bk_extension
end ResidualFrame
end Zigzag
```

### `EndpointFrameAction.lean`

```lean
import EndpointFrames
import FenceEndpointAction

namespace Zigzag
open Equiv
namespace EndpointFrame
variable {r : ℕ} (F : EndpointFrame r)

theorem pad_factor (w : Perm (Fin r)) :
    F.pad w = (padA w).trans ((splitAVertices r).trans F.vertices.symm) := by
  ext a
  simp [pad, padA]

theorem rawSwap_pad (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    rawSwap (i + 1) (by omega : i + 1 + 1 < r + 2) (F.pad w) =
      F.pad (rawSwap i hi w) := by
  rw [F.pad_factor w, F.pad_factor (rawSwap i hi w)]
  have hh := congrArg (fun e : Perm (Fin (r + 2)) =>
    e.trans ((splitAVertices r).trans F.vertices.symm)) (rawSwap_padA i hi w)
  simpa only [rawSwap, Equiv.trans_assoc] using hh

theorem incomparable_pad (i : ℕ) (hi : i + 1 < r) (w : Perm (Fin r)) :
    incomparable (zigLt (r + 2)) (i + 1) (by omega : i + 1 + 1 < r + 2) (F.pad w) ↔
      incomparable (zigLt r) i hi w := by
  have hl : leftPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (leftPos i hi).castSucc.succ := by ext; simp [leftPos]
  have hr : rightPos (i + 1) (by omega : i + 1 + 1 < r + 2) =
      (rightPos i hi).castSucc.succ := by ext; simp [rightPos]
  simp only [incomparable, hl, hr, pad_middle, F.middle_rel]

theorem bk_extension (i : ℕ) (hi : i + 1 < r) (w : ZigzagLE r) :
    bk (r + 2) (i + 1) (by omega) (F.extension w) = F.extension (bk r i hi w) := by
  apply Subtype.ext
  change (move (zigLt (r + 2)) (i + 1) _ (F.extension w)).val = F.pad ((bk r i hi w).val)
  rw [move_apply]
  change (if incomparable (zigLt (r + 2)) (i + 1) _ (F.pad w.val) then _ else _) = _
  rw [show (bk r i hi w).val = _ from move_apply (zigLt r) i hi w]
  by_cases h : incomparable (zigLt r) i hi w.val
  · simp only [(F.incomparable_pad i hi w.val).mpr h, ite_true, h]
    exact F.rawSwap_pad i hi w.val
  · simp only [(F.incomparable_pad i hi w.val).not.mpr h, ite_false, h]
    rfl

#print axioms bk_extension
end EndpointFrame
end Zigzag
```

### `FenceResidueMaps.lean`

```lean
import FenceGeometry
import Mathlib.Order.RelIso.Basic

namespace Zigzag

abbrev AResidue (r : ℕ) := {v : Fin (r + 2) // v.val ≠ 0 ∧ v.val ≠ 1}
abbrev BResidue (r : ℕ) := {v : Fin (r + 2) // v.val ≠ 0 ∧ v.val ≠ r + 1}
abbrev CResidue (r : ℕ) := {v : Fin (r + 2) // v.val ≠ r ∧ v.val ≠ r + 1}

/-- Source coordinate A: j ↦ j+2. -/
def residueA (r : ℕ) : Fin r ≃ AResidue r where
  toFun a := ⟨⟨a.val + 2, by omega⟩, by dsimp; omega, by dsimp; omega⟩
  invFun v := ⟨v.val.val - 2, by have := v.val.isLt; omega⟩
  left_inv a := by ext; dsimp; omega
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have := v.property
    dsimp
    omega

/-- Source coordinate B: j ↦ n-j in one-based notation. -/
def residueB (r : ℕ) : Fin r ≃ BResidue r where
  toFun a := ⟨⟨r - a.val, by omega⟩, by dsimp; omega, by dsimp; omega⟩
  invFun v := ⟨r - v.val.val, by
    have := v.val.isLt
    have := v.property
    omega⟩
  left_inv a := by ext; dsimp; omega
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have := v.val.isLt
    have := v.property
    dsimp
    omega

/-- Source coordinate C: j ↦ j. -/
def residueC (r : ℕ) : Fin r ≃ CResidue r where
  toFun a := ⟨⟨a.val, by omega⟩, by dsimp; omega, by dsimp; omega⟩
  invFun v := ⟨v.val.val, by
    have := v.val.isLt
    have := v.property
    omega⟩
  left_inv a := rfl
  right_inv v := by rfl

@[simp] theorem residueA_value (r : ℕ) (a : Fin r) :
    (residueA r a).val.val = a.val + 2 := rfl
@[simp] theorem residueB_value (r : ℕ) (a : Fin r) :
    (residueB r a).val.val = r - a.val := rfl
@[simp] theorem residueC_value (r : ℕ) (a : Fin r) :
    (residueC r a).val.val = a.val := rfl

/-- All three residual coordinate maps preserve the actual strict order. -/
def residueA_relIso (r : ℕ) :
    (zigLt r) ≃r (fun a b : AResidue r => zigLt (r + 2) a.val b.val) where
  toEquiv := residueA r
  map_rel_iff' := fun {a b} => zigLt_shift_two r a b

def residueB_relIso (r : ℕ) (hr : Even r) :
    (zigLt r) ≃r (fun a b : BResidue r => zigLt (r + 2) a.val b.val) where
  toEquiv := residueB r
  map_rel_iff' := fun {a b} => zigLt_reflect_interior r hr a b

def residueC_relIso (r : ℕ) :
    (zigLt r) ≃r (fun a b : CResidue r => zigLt (r + 2) a.val b.val) where
  toEquiv := residueC r
  map_rel_iff' := fun {a b} => zigLt_include_two r a b

#print axioms residueA_relIso
#print axioms residueB_relIso
#print axioms residueC_relIso
end Zigzag
```

### `FenceEndpointFrames.lean`

```lean
import EndpointFrames
import FenceResidueMaps

namespace Zigzag
open Equiv

/-- A framing is the existing source A coordinate map. -/
def frameA (r : ℕ) : EndpointFrame r where
  vertices := splitAVertices r
  first_min := by
    intro a h
    have hp : (splitAVertices r).symm none = 0 := by
      simp [splitAVertices, ← Equiv.optionCongr_symm]
    rw [hp] at h
    obtain ⟨ha, hb⟩ := h
    change a.val % 2 = 0 at ha
    change 0 = a.val + 1 ∨ a.val = 0 + 1 at hb
    omega
  last_max := by intro b h; have := h.1; simp [splitAVertices,
    ← Equiv.optionCongr_symm] at this
  middle_rel := by
    intro a b
    simp [splitAVertices, ← Equiv.optionCongr_symm, zigLt, Nat.add_assoc]

@[simp] theorem frameA_extension {r : ℕ} (w : ZigzagLE r) :
    (frameA r).extension w = endpointA w := rfl

/-- Source B: first vertex 1, last vertex n, and middle vertex map j ↦ n-j. -/
def splitBVertices (r : ℕ) : Fin (r + 2) ≃ Option (Option (Fin r)) :=
  (splitPositions r).trans (optionCongr (optionCongr (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ : Perm (Fin r))))

@[simp] theorem splitB_first (r : ℕ) : (splitBVertices r).symm none = 0 := by
  simp [splitBVertices, splitPositions, ← Equiv.optionCongr_symm]

@[simp] theorem splitB_last (r : ℕ) :
    (splitBVertices r).symm (some none) = Fin.last (r + 1) := by
  simp [splitBVertices, splitPositions, ← Equiv.optionCongr_symm]

@[simp] theorem splitB_middle (r : ℕ) (a : Fin r) :
    (splitBVertices r).symm (some (some a)) = ⟨r - a.val, by omega⟩ := by
  apply Fin.ext
  simp [splitBVertices, splitPositions, ← Equiv.optionCongr_symm]
  omega

def frameB (r : ℕ) (hr : Even r) : EndpointFrame r where
  vertices := splitBVertices r
  first_min := by
    intro a h
    rw [splitB_first] at h
    obtain ⟨ha, hb⟩ := h
    change a.val % 2 = 0 at ha
    change 0 = a.val + 1 ∨ a.val = 0 + 1 at hb
    omega
  last_max := by
    intro b h
    rw [splitB_last] at h
    have := h.1
    have hrmod : r % 2 = 0 := by obtain ⟨m, hm⟩ := hr; omega
    change (r + 1) % 2 = 0 at this
    omega
  middle_rel := by
    intro a b
    rw [splitB_middle, splitB_middle]
    exact zigLt_reflect_interior r hr a b

/-- Source C: first vertex n-1, last vertex n, middle map j ↦ j. -/
def splitCVertices (r : ℕ) : Fin (r + 2) ≃ Option (Option (Fin r)) :=
  ((finSuccEquivLast).trans (optionCongr finSuccEquivLast)).trans
    (Equiv.swap none (some none))

@[simp] theorem splitC_first (r : ℕ) :
    (splitCVertices r).symm none = ⟨r, by omega⟩ := by
  simp [splitCVertices, ← Equiv.optionCongr_symm]
  rfl

@[simp] theorem splitC_last (r : ℕ) :
    (splitCVertices r).symm (some none) = Fin.last (r + 1) := by
  simp [splitCVertices, ← Equiv.optionCongr_symm]

@[simp] theorem splitC_middle (r : ℕ) (a : Fin r) :
    (splitCVertices r).symm (some (some a)) = ⟨a.val, by omega⟩ := by
  simp [splitCVertices, ← Equiv.optionCongr_symm, Equiv.swap_apply_def]
  rfl

def frameC (r : ℕ) (hr : Even r) : EndpointFrame r where
  vertices := splitCVertices r
  first_min := by
    intro a h
    rw [splitC_first] at h
    have ha := h.1
    have hb := h.2
    have hrmod : r % 2 = 0 := by obtain ⟨m, hm⟩ := hr; omega
    change a.val % 2 = 0 at ha
    change r = a.val + 1 ∨ a.val = r + 1 at hb
    omega
  last_max := by
    intro b h
    rw [splitC_last] at h
    have := h.1
    have hrmod : r % 2 = 0 := by obtain ⟨m, hm⟩ := hr; omega
    change (r + 1) % 2 = 0 at this
    omega
  middle_rel := by
    intro a b
    rw [splitC_middle, splitC_middle]
    exact zigLt_include_two r a b

def endpointB {r : ℕ} (hr : Even r) : ZigzagLE r → ZigzagLE (r + 2) :=
  (frameB r hr).extension

def endpointC {r : ℕ} (hr : Even r) : ZigzagLE r → ZigzagLE (r + 2) :=
  (frameC r hr).extension

/-- All three maps now cover their full literal endpoint fibers. -/
noncomputable def endpointAEquiv (r : ℕ) := (frameA r).fiberEquiv
noncomputable def endpointBEquiv (r : ℕ) (hr : Even r) := (frameB r hr).fiberEquiv
noncomputable def endpointCEquiv (r : ℕ) (hr : Even r) := (frameC r hr).fiberEquiv

@[simp] theorem endpointB_first {r : ℕ} (hr : Even r) (w : ZigzagLE r) :
    (endpointB hr w).val 0 = 0 := by
  exact (frameB r hr).pad_first w.val |>.trans (splitB_first r)
@[simp] theorem endpointB_last {r : ℕ} (hr : Even r) (w : ZigzagLE r) :
    (endpointB hr w).val (Fin.last (r + 1)) = Fin.last (r + 1) := by
  exact (frameB r hr).pad_last w.val |>.trans (splitB_last r)
@[simp] theorem endpointB_middle {r : ℕ} (hr : Even r) (w : ZigzagLE r) (a : Fin r) :
    (endpointB hr w).val a.castSucc.succ = ⟨r - (w.val a).val, by omega⟩ :=
  (frameB r hr).pad_middle w.val a |>.trans (splitB_middle r (w.val a))
@[simp] theorem endpointC_first {r : ℕ} (hr : Even r) (w : ZigzagLE r) :
    (endpointC hr w).val 0 = ⟨r, by omega⟩ :=
  (frameC r hr).pad_first w.val |>.trans (splitC_first r)
@[simp] theorem endpointC_last {r : ℕ} (hr : Even r) (w : ZigzagLE r) :
    (endpointC hr w).val (Fin.last (r + 1)) = Fin.last (r + 1) :=
  (frameC r hr).pad_last w.val |>.trans (splitC_last r)
@[simp] theorem endpointC_middle {r : ℕ} (hr : Even r) (w : ZigzagLE r) (a : Fin r) :
    (endpointC hr w).val a.castSucc.succ = ⟨(w.val a).val, by omega⟩ :=
  (frameC r hr).pad_middle w.val a |>.trans (splitC_middle r (w.val a))

#print axioms endpointAEquiv
#print axioms endpointBEquiv
#print axioms endpointCEquiv
end Zigzag
```

### `FenceInternalLifts.lean`

```lean
import EndpointFrameAction
import FenceEndpointFrames

namespace Zigzag
open Equiv

/-- Source H=⟨t₂,...,t_(n-2)⟩. -/
def internalBK (r : ℕ) : Subgroup (Perm (ZigzagLE (r + 2))) :=
  Subgroup.closure {g | ∃ (i : ℕ) (hi : i + 1 < r),
    g = bk (r + 2) (i + 1) (by omega)}

theorem internalBK_le (r : ℕ) : internalBK r ≤ BKgroup (r + 2) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, hi, rfl⟩
  exact bk_mem _ _ _

/-- Every smaller BK permutation lifts with the SAME action on every framed
fiber. The lift is not asserted to fix any other fiber. -/
theorem simultaneous_internal_lift {r : ℕ} {J : Type*} (F : J → EndpointFrame r)
    (g : Perm (ZigzagLE r)) (hg : g ∈ BKgroup r) :
    ∃ h ∈ internalBK r, ∀ j w, h ((F j).extension w) = (F j).extension (g w) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact ⟨bk (r + 2) (i + 1) (by omega),
      Subgroup.subset_closure ⟨i, hi, rfl⟩, fun j w => (F j).bk_extension i hi w⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun _ _ => rfl⟩
  | mul g g' _ _ ih ih' =>
    obtain ⟨h, hh, hact⟩ := ih
    obtain ⟨h', hh', hact'⟩ := ih'
    refine ⟨h * h', Subgroup.mul_mem _ hh hh', ?_⟩
    intro j w
    change h (h' ((F j).extension w)) = (F j).extension (g (g' w))
    rw [hact', hact]
  | inv g _ ih =>
    obtain ⟨h, hh, hact⟩ := ih
    refine ⟨h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
    intro j w
    apply h.injective
    simpa only [Perm.inv_def, Equiv.apply_symm_apply] using (hact j (g⁻¹ w)).symm

/-- Conversely, internal words act synchronously on every framed fiber. -/
theorem internal_action_exists {r : ℕ} {J : Type*} (F : J → EndpointFrame r)
    (h : Perm (ZigzagLE (r + 2))) (hh : h ∈ internalBK r) :
    ∃ g ∈ BKgroup r, ∀ j w, h ((F j).extension w) = (F j).extension (g w) := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨i, hi, rfl⟩ := hh
    exact ⟨bk r i hi, bk_mem _ _ _, fun j w => (F j).bk_extension i hi w⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun _ _ => rfl⟩
  | mul h h' _ _ ih ih' =>
    obtain ⟨g, hg, hact⟩ := ih
    obtain ⟨g', hg', hact'⟩ := ih'
    refine ⟨g * g', Subgroup.mul_mem _ hg hg', ?_⟩
    intro j w
    change h (h' ((F j).extension w)) = (F j).extension (g (g' w))
    rw [hact', hact]
  | inv h _ ih =>
    obtain ⟨g, hg, hact⟩ := ih
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    intro j w
    apply h.injective
    simpa only [Perm.inv_def, Equiv.apply_symm_apply] using (hact j (g⁻¹ w)).symm

/-- The three actual coordinate maps, not abstract copies of their sizes. -/
def connectedFrames (r : ℕ) (hr : Even r) : Fin 3 → EndpointFrame r :=
  ![frameA r, frameB r hr, frameC r hr]

/-- Induction gives the full diagonal image on A,B,C before section isolation. -/
theorem diagonal_image_full {r : ℕ} (hr : Even r) (ih : BKgroup r = ⊤)
    (g : Perm (ZigzagLE r)) :
    ∃ h ∈ internalBK r,
      (∀ w, h (endpointA w) = endpointA (g w)) ∧
      (∀ w, h (endpointB hr w) = endpointB hr (g w)) ∧
      (∀ w, h (endpointC hr w) = endpointC hr (g w)) := by
  obtain ⟨h, hh, hact⟩ := simultaneous_internal_lift (connectedFrames r hr) g (by rw [ih]; trivial)
  exact ⟨h, hh, hact 0, hact 1, hact 2⟩

#print axioms simultaneous_internal_lift
#print axioms internal_action_exists
#print axioms diagonal_image_full
end Zigzag
```

### `FenceInternalProjection.lean`

```lean
import FenceInternalLifts

namespace Zigzag
open Equiv

private theorem internal_action_all {r : ℕ} (h : internalBK r) :
    ∃ g ∈ BKgroup r, ∀ (F : EndpointFrame r) w,
      h.val (F.extension w) = F.extension (g w) :=
  internal_action_exists (fun F : EndpointFrame r => F) h.val h.property

/-- The smaller permutation induced by an internal word, with its actual action
on every endpoint frame as the uniqueness specification. -/
noncomputable def internalCoordinate {r : ℕ} (h : internalBK r) : Perm (ZigzagLE r) :=
  (internal_action_all h).choose

theorem internalCoordinate_mem {r : ℕ} (h : internalBK r) :
    internalCoordinate h ∈ BKgroup r := (internal_action_all h).choose_spec.1

theorem internalCoordinate_action {r : ℕ} (h : internalBK r) (F : EndpointFrame r)
    (w : ZigzagLE r) : h.val (F.extension w) = F.extension (internalCoordinate h w) :=
  (internal_action_all h).choose_spec.2 F w

/-- Restriction to the A fiber determines the smaller permutation uniquely. -/
theorem internalCoordinate_unique {r : ℕ} (h : internalBK r) (g : Perm (ZigzagLE r))
    (hg : ∀ w, h.val (endpointA w) = endpointA (g w)) : internalCoordinate h = g := by
  apply Equiv.ext
  intro w
  apply endpointA_injective r
  exact (internalCoordinate_action h (frameA r) w).symm.trans (hg w)

noncomputable def internalProjection (r : ℕ) : internalBK r →* Perm (ZigzagLE r) where
  toFun := internalCoordinate
  map_one' := internalCoordinate_unique 1 1 (fun _ => rfl)
  map_mul' h k := by
    apply internalCoordinate_unique
    intro w
    change h.val (k.val (endpointA w)) = endpointA (internalCoordinate h (internalCoordinate k w))
    have ha (k : internalBK r) (v : ZigzagLE r) :
        k.val (endpointA v) = endpointA (internalCoordinate k v) :=
      internalCoordinate_action k (frameA r) v
    rw [ha k, ha h]

theorem internalProjection_action {r : ℕ} (h : internalBK r) (F : EndpointFrame r)
    (w : ZigzagLE r) : h.val (F.extension w) = F.extension (internalProjection r h w) :=
  internalCoordinate_action h F w

/-- Its image is exactly the smaller BK group, without any induction hypothesis. -/
theorem internalProjection_range (r : ℕ) : (internalProjection r).range = BKgroup r := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    exact internalCoordinate_mem h
  · intro g hg
    obtain ⟨h, hh, hact⟩ := simultaneous_internal_lift (fun F : EndpointFrame r => F) g hg
    exact ⟨⟨h, hh⟩, internalCoordinate_unique ⟨h, hh⟩ g (hact (frameA r))⟩

theorem internalProjection_surjective {r : ℕ} (ih : BKgroup r = ⊤) :
    Function.Surjective (internalProjection r) := by
  intro g
  have hg : g ∈ (internalProjection r).range := by rw [internalProjection_range, ih]; trivial
  exact hg

/-- The union U of the three source fibers. -/
def InConnectedFibers {r : ℕ} (hr : Even r) (w : ZigzagLE (r + 2)) : Prop :=
  ∃ (j : Fin 3) (v : ZigzagLE r), w = (connectedFrames r hr j).extension v

def BadFiberWords (r : ℕ) (hr : Even r) :=
  {w : ZigzagLE (r + 2) // ¬ InConnectedFibers hr w}

theorem internal_preserves_connected {r : ℕ} (hr : Even r) (h : internalBK r)
    (w : ZigzagLE (r + 2)) :
    InConnectedFibers hr (h.val w) ↔ InConnectedFibers hr w := by
  have forward (k : internalBK r) (v : ZigzagLE (r + 2))
      (hv : InConnectedFibers hr v) : InConnectedFibers hr (k.val v) := by
    obtain ⟨j, x, rfl⟩ := hv
    exact ⟨j, internalProjection r k x, internalProjection_action k _ x⟩
  constructor
  · intro hw
    have hh := forward h⁻¹ (h.val w) hw
    simpa only [Subgroup.coe_inv, Perm.inv_def, Equiv.symm_apply_apply] using hh
  · exact forward h w

/-- The action on ALL remaining fibers, with its actual image used as codomain
in the simple-section argument (the ambient symmetric group would be too large). -/
noncomputable def badAction (r : ℕ) (hr : Even r) :
    internalBK r →* Perm (BadFiberWords r hr) where
  toFun h := h.val.subtypePerm (fun w => not_congr (internal_preserves_connected hr h w))
  map_one' := by ext w; rfl
  map_mul' _ _ := by ext w; rfl

@[simp] theorem badAction_apply {r : ℕ} (hr : Even r) (h : internalBK r)
    (w : BadFiberWords r hr) : (badAction r hr h w).val = h.val w.val := rfl

#print axioms internalProjection
#print axioms internalProjection_range
#print axioms internalProjection_surjective
#print axioms internal_preserves_connected
#print axioms badAction
end Zigzag
```

### `ResidualRestriction.lean`

```lean
import ResidualFrameAction
import FenceInternalProjection

namespace Zigzag
open Equiv
namespace ResidualFrame
variable {r : ℕ} (F : ResidualFrame r)

/-- Internal words induce exactly words in the BK generators of the residual
relation, even when that relation is disconnected. -/
theorem internal_action_exists (h : Perm (ZigzagLE (r + 2))) (hh : h ∈ internalBK r) :
    ∃ g ∈ relationBK F.relation, ∀ w, h (F.extension w) = F.extension (g w) := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨i, hi, rfl⟩ := hh
    exact ⟨move F.relation i hi, Subgroup.subset_closure ⟨i, hi, rfl⟩,
      fun w => F.bk_extension i hi w⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun _ => rfl⟩
  | mul h h' _ _ ih ih' =>
    obtain ⟨g, hg, hact⟩ := ih
    obtain ⟨g', hg', hact'⟩ := ih'
    refine ⟨g * g', Subgroup.mul_mem _ hg hg', ?_⟩
    intro w
    change h (h' (F.extension w)) = F.extension (g (g' w))
    rw [hact', hact]
  | inv h _ ih =>
    obtain ⟨g, hg, hact⟩ := ih
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    intro w
    apply h.injective
    simpa only [Perm.inv_def, Equiv.apply_symm_apply] using (hact (g⁻¹ w)).symm

noncomputable def coordinate (h : internalBK r) : Perm (LinearExtensions F.relation) :=
  (F.internal_action_exists h.val h.property).choose

theorem coordinate_mem (h : internalBK r) : F.coordinate h ∈ relationBK F.relation :=
  (F.internal_action_exists h.val h.property).choose_spec.1

theorem coordinate_action (h : internalBK r) (w : LinearExtensions F.relation) :
    h.val (F.extension w) = F.extension (F.coordinate h w) :=
  (F.internal_action_exists h.val h.property).choose_spec.2 w

theorem coordinate_unique (h : internalBK r) (g : Perm (LinearExtensions F.relation))
    (hg : ∀ w, h.val (F.extension w) = F.extension (g w)) : F.coordinate h = g := by
  apply Equiv.ext
  intro w
  apply F.extension_injective
  exact (F.coordinate_action h w).symm.trans (hg w)

/-- Restriction in literal residual coordinates, with its image in the
residual BK group, rather than the full symmetric group of the fiber. -/
noncomputable def restriction : internalBK r →* relationBK F.relation where
  toFun h := ⟨F.coordinate h, F.coordinate_mem h⟩
  map_one' := Subtype.ext (F.coordinate_unique 1 1 (fun _ => rfl))
  map_mul' h k := by
    apply Subtype.ext
    apply F.coordinate_unique
    intro w
    change h.val (k.val (F.extension w)) = F.extension (F.coordinate h (F.coordinate k w))
    rw [F.coordinate_action, F.coordinate_action]

@[simp] theorem restriction_action (h : internalBK r) (w : LinearExtensions F.relation) :
    h.val (F.extension w) = F.extension ((F.restriction h).val w) :=
  F.coordinate_action h w

/-- No subgroup of the residual BK group is lost in restriction: every residual
word lifts to the same internal word on the whole fence. -/
theorem restriction_surjective : Function.Surjective F.restriction := by
  rintro ⟨g, hg⟩
  suffices ∃ h ∈ internalBK r, ∀ w, h (F.extension w) = F.extension (g w) by
    obtain ⟨h, hh, ha⟩ := this
    exact ⟨⟨h, hh⟩, Subtype.ext (F.coordinate_unique ⟨h, hh⟩ g ha)⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact ⟨bk (r + 2) (i + 1) (by omega), Subgroup.subset_closure ⟨i, hi, rfl⟩,
      fun w => F.bk_extension i hi w⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun _ => rfl⟩
  | mul g g' _ _ ih ih' =>
    obtain ⟨h, hh, ha⟩ := ih
    obtain ⟨h', hh', ha'⟩ := ih'
    refine ⟨h * h', Subgroup.mul_mem _ hh hh', ?_⟩
    intro w
    change h (h' (F.extension w)) = F.extension (g (g' w))
    rw [ha', ha]
  | inv g _ ih =>
    obtain ⟨h, hh, ha⟩ := ih
    refine ⟨h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
    intro w
    apply h.injective
    simpa only [Perm.inv_def, Equiv.apply_symm_apply] using (ha (g⁻¹ w)).symm

#print axioms restriction
#print axioms restriction_surjective
end ResidualFrame
end Zigzag
```

### `ResidualWordFrames.lean`

```lean
import ResidualRestriction

namespace Zigzag
open Equiv
namespace ResidualFrame

/-- A word supplies coordinates on its whole endpoint fiber. Repeated frames
are intentional: indexing by words avoids any noncanonical enumeration of
admissible endpoint pairs and still gives a finite faithful product action. -/
def ofWord {r : ℕ} (w : ZigzagLE (r + 2)) : ResidualFrame r where
  vertices := w.val.symm.trans (splitPositions r)
  first_min := by
    intro a ha
    have he : ((w.val.symm.trans (splitPositions r)).symm none) = w.val 0 := by
      simp [splitPositions, ← optionCongr_symm]
    rw [he] at ha
    have hh := w.property _ _ ha
    simp only [Equiv.symm_apply_apply, Fin.not_lt_zero] at hh
  last_max := by
    intro b hb
    have he : ((w.val.symm.trans (splitPositions r)).symm (some none)) =
        w.val (Fin.last (r + 1)) := by
      simp [splitPositions, ← optionCongr_symm]
    rw [he] at hb
    have hh := w.property _ _ hb
    rw [Equiv.symm_apply_apply] at hh
    exact (not_lt_of_ge (Fin.le_last _)) hh

@[simp] theorem ofWord_first {r : ℕ} (w : ZigzagLE (r + 2)) :
    (ofWord w).vertices.symm none = w.val 0 := by
  simp [ofWord, splitPositions, ← optionCongr_symm]

@[simp] theorem ofWord_last {r : ℕ} (w : ZigzagLE (r + 2)) :
    (ofWord w).vertices.symm (some none) = w.val (Fin.last (r + 1)) := by
  simp [ofWord, splitPositions, ← optionCongr_symm]

/-- The seed word is in the FULL fiber enumerated by its residual frame. -/
theorem ofWord_covers {r : ℕ} (w : ZigzagLE (r + 2)) :
    ∃ v, (ofWord w).extension v = w := by
  exact (ofWord w).exists_pad ⟨w, (ofWord_first w).symm, (ofWord_last w).symm⟩

#print axioms ofWord
#print axioms ofWord_covers
end ResidualFrame
end Zigzag
```

### `SectionFreeImage.lean`

```lean
import SectionFree

namespace Zigzag

/-- A range is section-free if its action is determined by another action
whose target is section-free. Surjectivity onto the determining target is
unnecessary: its actual image is enough. -/
theorem sectionFree_range_of_ker_le {S G B D : Type*}
    [Group S] [Group G] [Group B] [Group D]
    (p : G →* B) (q : G →* D) (hker : p.ker ≤ q.ker)
    (hB : SectionFree S B) : SectionFree S q.range := by
  have hle : p.rangeRestrict.ker ≤ q.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using hker
  let f : p.range →* q.range := p.rangeRestrict.liftOfSurjective
    p.rangeRestrict_surjective ⟨q.rangeRestrict, hle⟩
  have hf (g : G) : f (p.rangeRestrict g) = q.rangeRestrict g :=
    p.rangeRestrict.liftOfRightInverse_comp_apply
      (Function.surjInv p.rangeRestrict_surjective)
      (Function.rightInverse_surjInv p.rangeRestrict_surjective)
      ⟨q.rangeRestrict, hle⟩ g
  apply sectionFree_quotient f _ (sectionFree_subgroup hB p.range)
  intro x
  obtain ⟨g, rfl⟩ := q.rangeRestrict_surjective x
  exact ⟨p.rangeRestrict g, hf g⟩

#print axioms sectionFree_range_of_ker_le
end Zigzag
```

### `FenceCountGrowth.lean`

```lean
import FenceEndpointFrames
import ZigzagCounts
import Mathlib.Data.Fintype.Sum

namespace Zigzag

/-- Padding A alone gives monotonicity by two, for every order. -/
theorem card_mono_two (r : ℕ) :
    Fintype.card (ZigzagLE r) ≤ Fintype.card (ZigzagLE (r + 2)) :=
  Fintype.card_le_of_injective endpointA (endpointA_injective r)

/-- The A and C images are disjoint as soon as r is positive: their first
vertices are respectively 0 and r. -/
theorem endpointA_ne_endpointC {r : ℕ} (hr : Even r) (hpos : 0 < r)
    (w v : ZigzagLE r) : endpointA w ≠ endpointC hr v := by
  intro he
  have hh := congrArg (fun x : ZigzagLE (r + 2) => (x.val 0).val) he
  have hf : (endpointA w).val 0 = 0 := padA_first w.val
  rw [hf, endpointC_first] at hh
  change 0 = r at hh
  omega

/-- Two disjoint literal endpoint embeddings double the even-order count. -/
theorem card_double_le {r : ℕ} (hr : Even r) (hpos : 0 < r) :
    2 * Fintype.card (ZigzagLE r) ≤ Fintype.card (ZigzagLE (r + 2)) := by
  let f : ZigzagLE r ⊕ ZigzagLE r → ZigzagLE (r + 2) :=
    Sum.elim endpointA (endpointC hr)
  have hf : Function.Injective f := by
    intro x y he
    cases x with
    | inl w =>
      cases y with
      | inl v => exact congrArg Sum.inl (endpointA_injective r he)
      | inr v => exact False.elim (endpointA_ne_endpointC hr hpos w v he)
    | inr w =>
      cases y with
      | inl v => exact False.elim (endpointA_ne_endpointC hr hpos v w he.symm)
      | inr v => exact congrArg Sum.inr ((frameC r hr).extension_injective he)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sum, two_mul] using hh

/-- In every even order at least four, the extension set is larger than the
number of fence vertices. This is one of the source's two order separations. -/
theorem vertices_lt_card (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) :
    n < Fintype.card (ZigzagLE n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 4
    · subst n
      rw [card_zigzagLE_four]
      omega
    · have h6 : 6 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
      have hs : n - 2 + 2 = n := by omega
      have heven : Even (n - 2) := by
        obtain ⟨k, hk⟩ := hn
        exact ⟨k - 1, by omega⟩
      have hb := ih (n - 2) (by omega) heven (by omega)
      have hg := card_double_le heven (by omega : 0 < n - 2)
      rw [hs] at hg
      omega

theorem five_le_card (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) :
    5 ≤ Fintype.card (ZigzagLE n) := by
  have := vertices_lt_card n hn h4
  omega

#print axioms card_double_le
#print axioms vertices_lt_card
#print axioms five_le_card
end Zigzag
```

### `FenceDiagonalIsolation.lean`

```lean
import FenceInternalProjection
import DiagonalIsolation
import FenceCountGrowth
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

namespace Zigzag
open Equiv

/-- The remaining quantitative section obligation, on the actual bad-fiber
image. This definition is NOT asserted unconditionally in this module. -/
def BadImageSectionFree (r : ℕ) (hr : Even r) : Prop :=
  SectionFree (alternatingGroup (ZigzagLE r)) (badAction r hr).range

/-- With the residual section obligation supplied, diagonal isolation is now a
literal fence theorem: it supplies all three synchronized actions and fixes
EVERY word outside their union. -/
theorem diagonal_isolation_of_bad_sectionFree {r : ℕ} (hr : Even r)
    (h4 : 4 ≤ r) (ih : BKgroup r = ⊤)
    (hbad : BadImageSectionFree r hr) (a : alternatingGroup (ZigzagLE r)) :
    ∃ h ∈ BKgroup (r + 2),
      (∀ w, h (endpointA w) = endpointA (a.val w)) ∧
      (∀ w, h (endpointB hr w) = endpointB hr (a.val w)) ∧
      (∀ w, h (endpointC hr w) = endpointC hr (a.val w)) ∧
      (∀ w, ¬ InConnectedFibers hr w → h w = w) := by
  let : IsSimpleGroup (alternatingGroup (ZigzagLE r)) :=
    alternatingGroup.isSimpleGroup (by simpa only [Nat.card_eq_fintype_card] using five_le_card r hr h4)
  obtain ⟨h, hp, hq⟩ := isolate_simple_subgroup (internalProjection r)
    (internalProjection_surjective ih) (badAction r hr).rangeRestrict
    (alternatingGroup (ZigzagLE r)) hbad a
  refine ⟨h.val, internalBK_le r h.property, ?_, ?_, ?_, ?_⟩
  · intro w
    simpa only [hp, frameA_extension] using internalProjection_action h (frameA r) w
  · intro w
    change h.val ((frameB r hr).extension w) = (frameB r hr).extension (a.val w)
    rw [internalProjection_action, hp]
  · intro w
    change h.val ((frameC r hr).extension w) = (frameC r hr).extension (a.val w)
    rw [internalProjection_action, hp]
  · intro w hw
    have he : badAction r hr h = 1 := congrArg Subtype.val hq
    have hh := Equiv.congr_fun he (⟨w, hw⟩ : BadFiberWords r hr)
    exact congrArg Subtype.val hh

#print axioms diagonal_isolation_of_bad_sectionFree
end Zigzag
```

### `BadFiberReduction.lean`

```lean
import ResidualWordFrames
import SectionFreeImage
import FenceDiagonalIsolation

namespace Zigzag
open Equiv

/-- The finite product of the ACTUAL residual BK actions on bad endpoint
fibers. No full symmetric group of a bad fiber is used as a bound. -/
noncomputable def badResidualProduct (r : ℕ) (hr : Even r) :
    internalBK r →* ∀ w : BadFiberWords r hr,
      relationBK (ResidualFrame.ofWord w.val).relation where
  toFun h w := (ResidualFrame.ofWord w.val).restriction h
  map_one' := by funext w; exact map_one _
  map_mul' h k := by funext w; exact map_mul _ h k

/-- Fixing all residual coordinates fixes every bad word, because that word
belongs to the full fiber of its own frame. This proves faithfulness of the
combined restriction for exactly the complement image needed by isolation. -/
theorem badResidualProduct_ker_le (r : ℕ) (hr : Even r) :
    (badResidualProduct r hr).ker ≤ (badAction r hr).ker := by
  intro h hh
  apply Equiv.ext
  intro w
  apply Subtype.ext
  change h.val w.val = w.val
  obtain ⟨v, hv⟩ := ResidualFrame.ofWord_covers w.val
  have hc : (ResidualFrame.ofWord w.val).restriction h = 1 :=
    congrFun hh w
  rw [← hv, ResidualFrame.restriction_action, hc]
  rfl

/-- The bad-image obligation is reduced to the disconnected residual BK
section bounds. This theorem contains no induction or parity hypothesis. -/
theorem badImageSectionFree_of_residuals {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (hres : ∀ w : BadFiberWords r hr,
      SectionFree (alternatingGroup (ZigzagLE r))
        (relationBK (ResidualFrame.ofWord w.val).relation)) :
    BadImageSectionFree r hr := by
  classical
  let : Finite (BadFiberWords r hr) := inferInstanceAs (Finite {w // ¬ InConnectedFibers hr w})
  let : IsSimpleGroup (alternatingGroup (ZigzagLE r)) :=
    alternatingGroup.isSimpleGroup (by
      simpa only [Nat.card_eq_fintype_card] using five_le_card r hr h4)
  exact sectionFree_range_of_ker_le (badResidualProduct r hr) (badAction r hr)
    (badResidualProduct_ker_le r hr)
    (sectionFree_pi (fun w : BadFiberWords r hr =>
      relationBK (ResidualFrame.ofWord w.val).relation) hres)

#print axioms badResidualProduct_ker_le
#print axioms badImageSectionFree_of_residuals
end Zigzag
```

### `ShuffleCoordinates.lean`

```lean
import PosetShufflePacket
import Mathlib.Data.Fintype.Sort
import Mathlib.Logic.Equiv.Sigma

namespace Zigzag
open Equiv
namespace PosetShuffle

variable {r k : ℕ} (c : Fin r → Fin k)

abbrev Fiber (s : Fin r → Fin k) (j : Fin k) := {p : Fin r // s p = j}

/-- A literal component-label word with the prescribed multiplicities. -/
def Word := {s : Fin r → Fin k // ∀ j, Fintype.card (Fiber s j) = Fintype.card (Fiber c j)}

instance : Fintype (Word c) := by unfold Word; infer_instance

/-- Occurrences are enumerated in position order, not by an arbitrary bijection. -/
noncomputable def occurrence (s : Word c) (j : Fin k) :
    Fin (Fintype.card (Fiber c j)) ≃o Fiber s.val j :=
  monoEquivOfFin _ (s.property j)

/-- The restriction of a permutation to the inverse images of a component. -/
def restrict (w : Perm (Fin r)) (j : Fin k) : Fiber (c ∘ w) j ≃ Fiber c j where
  toFun p := ⟨w p.val, p.property⟩
  invFun v := ⟨w.symm v.val, by simpa using v.property⟩
  left_inv p := by ext; simp
  right_inv v := by ext; simp

def labels (w : Perm (Fin r)) : Word c :=
  ⟨c ∘ w, fun j => Fintype.card_congr (restrict c w j)⟩

noncomputable def internal (w : Perm (Fin r)) (j : Fin k) :
    Fin (Fintype.card (Fiber c j)) ≃ Fiber c j :=
  (occurrence c (labels c w) j).toEquiv.trans (restrict c w j)

@[simp] theorem internal_apply (w : Perm (Fin r)) (j : Fin k)
    (a : Fin (Fintype.card (Fiber c j))) :
    (internal c w j a).val = w (occurrence c (labels c w) j a).val := rfl

/-- Assemble an actual position-to-vertex permutation from shuffle/internal data. -/
noncomputable def assemble (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j) : Perm (Fin r) :=
  (sigmaFiberEquiv s.val).symm.trans
    ((Equiv.sigmaCongrRight fun j => (occurrence c s j).symm.toEquiv.trans (x j)).trans
      (sigmaFiberEquiv c))

@[simp] theorem assemble_at (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j)
    (j : Fin k) (p : Fiber s.val j) :
    assemble c s x p.val = (x j ((occurrence c s j).symm p)).val := by
  rcases p with ⟨p, hp⟩
  subst j
  rfl

@[simp] theorem assemble_symm_at (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j)
    (j : Fin k) (v : Fiber c j) :
    (assemble c s x).symm v.val =
      (occurrence c s j ((x j).symm v)).val := by
  rcases v with ⟨v, hv⟩
  subst j
  rfl

@[simp] theorem assemble_occurrence (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j)
    (j : Fin k) (a : Fin (Fintype.card (Fiber c j))) :
    assemble c s x (occurrence c s j a).val = (x j a).val := by
  rw [assemble_at]
  simp

@[simp] theorem labels_assemble (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j) :
    labels c (assemble c s x) = s := by
  apply Subtype.ext
  funext p
  change c (assemble c s x p) = s.val p
  rw [assemble_at c s x (s.val p) ⟨p, rfl⟩]
  exact (x _ _).property

@[simp] theorem internal_assemble (s : Word c)
    (x : ∀ j, Fin (Fintype.card (Fiber c j)) ≃ Fiber c j) :
    internal c (assemble c s x) = x := by
  funext j
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [internal_apply, labels_assemble, assemble_occurrence]

@[simp] theorem assemble_internal (w : Perm (Fin r)) :
    assemble c (labels c w) (internal c w) = w := by
  apply Equiv.ext
  intro p
  rw [assemble_at c (labels c w) (internal c w) (c (w p)) ⟨p, rfl⟩]
  simp only [internal_apply, OrderIso.apply_symm_apply]

variable {c} (R : Fin r → Fin r → Prop)

/-- Restriction to the increasing list of occurrences preserves the source
linear-extension condition exactly. -/
theorem internal_isLE (w : LinearExtensions R) (j : Fin k) :
    ∀ a b : Fiber c j, R a.val b.val →
      (internal c w.val j).symm a < (internal c w.val j).symm b := by
  intro a b hab
  apply (occurrence c (labels c w.val) j).symm.strictMono
  exact w.property a.val b.val hab

/-- With no cross-component order edges, assembly is a linear extension. -/
theorem assemble_isLE (hc : ∀ a b, R a b → c a = c b)
    (s : Word c) (x : ∀ j, ComponentLE R c j) :
    IsLE R (assemble c s (fun j => (x j).val)) := by
  intro a b hab
  have hc' := hc a b hab
  let a' : Fiber c (c a) := ⟨a, rfl⟩
  let b' : Fiber c (c a) := ⟨b, hc'.symm⟩
  rw [assemble_symm_at c s _ (c a) a', assemble_symm_at c s _ (c a) b']
  exact (occurrence c s (c a)).strictMono ((x (c a)).property a' b' hab)

noncomputable def encode (hc : ∀ a b, R a b → c a = c b) :
    LinearExtensions R ≃ Shuffle.State (Word c) (ComponentLE R c) where
  toFun w := (labels c w.val, fun j => ⟨internal c w.val j, internal_isLE R w j⟩)
  invFun u := ⟨assemble c u.1 (fun j => (u.2 j).val), assemble_isLE R hc u.1 u.2⟩
  left_inv w := by apply Subtype.ext; exact assemble_internal c w.val
  right_inv u := by
    apply Prod.ext
    · exact labels_assemble c u.1 _
    · funext j
      apply Subtype.ext
      exact congrFun (internal_assemble c u.1 (fun j => (u.2 j).val)) j

#print axioms encode
end PosetShuffle
end Zigzag
```

### `ShuffleProjection.lean`

```lean
import ShuffleKernel

namespace Zigzag.Shuffle
open Equiv
variable {Sh J : Type*} {X : J → Type*}
variable {P : Type*} [Group P] (q : P →* Perm Sh)

/-- Permutations whose first coordinate is induced by the position group. -/
def Projects (g : Perm (State Sh X)) : Prop :=
  ∃ τ : q.range, ∀ u, (g u).1 = τ.val u.1

theorem projects_one : Projects (X := X) q 1 := ⟨1, fun _ => rfl⟩

theorem projects_mul {g h : Perm (State Sh X)}
    (hg : Projects q g) (hh : Projects q h) : Projects q (g * h) := by
  obtain ⟨τ, hτ⟩ := hg
  obtain ⟨υ, hυ⟩ := hh
  exact ⟨τ * υ, fun u => by simp only [Perm.mul_apply, hτ, hυ]; rfl⟩

theorem projects_inv {g : Perm (State Sh X)} (hg : Projects q g) :
    Projects q g⁻¹ := by
  obtain ⟨τ, hτ⟩ := hg
  refine ⟨τ⁻¹, fun u => ?_⟩
  apply τ.val.injective
  rw [← hτ]
  change (g (g.symm u)).1 = τ.val (τ.val.symm u.1)
  simp only [Equiv.apply_symm_apply]

def projectingSubgroup : Subgroup (Perm (State Sh X)) where
  carrier := Projects q
  one_mem' := projects_one q
  mul_mem' := projects_mul q
  inv_mem' := projects_inv q

variable [∀ j, Nonempty (X j)]

theorem projection_unique (g : Perm (State Sh X)) (τ υ : Perm Sh)
    (hτ : ∀ u, (g u).1 = τ u.1) (hυ : ∀ u, (g u).1 = υ u.1) : τ = υ := by
  classical
  ext s
  let x : ∀ j, X j := fun j => Classical.choice (inferInstance : Nonempty (X j))
  exact (hτ (s, x)).symm.trans (hυ (s, x))

noncomputable def project : projectingSubgroup (X := X) q →* q.range where
  toFun g := Classical.choose g.property
  map_one' := by
    apply Subtype.ext
    exact projection_unique 1 _ _ (Classical.choose_spec (projects_one (X := X) q))
      (fun _ => rfl)
  map_mul' g h := by
    apply Subtype.ext
    apply projection_unique (g.val * h.val)
    · exact Classical.choose_spec (show Projects q (g.val * h.val) from (g * h).property)
    · intro u
      change (g.val (h.val u)).1 = _
      rw [Classical.choose_spec g.property (h.val u),
        Classical.choose_spec h.property u]
      rfl

@[simp] theorem project_apply (g : projectingSubgroup (X := X) q) (u : State Sh X) :
    (g.val u).1 = (project q g).val u.1 := Classical.choose_spec g.property u

/-- Any subgroup satisfying generator equivariance has the required shuffle
quotient. The codomain is literally a quotient image of the position group. -/
noncomputable def subgroupProject (G : Subgroup (Perm (State Sh X)))
    (hG : G ≤ projectingSubgroup q) : G →* q.range :=
  (project q).comp (Subgroup.inclusion hG)

theorem subgroupProject_fixes (G : Subgroup (Perm (State Sh X)))
    (hG : G ≤ projectingSubgroup q)
    (g : (subgroupProject q G hG).ker) (u : State Sh X) :
    (g.val.val u).1 = u.1 := by
  have h := project_apply q (Subgroup.inclusion hG g.val) u
  have he : subgroupProject q G hG g.val = 1 := g.property
  change (g.val.val u).1 = (subgroupProject q G hG g.val).val u.1 at h
  rw [he] at h
  exact h

#print axioms subgroupProject
#print axioms subgroupProject_fixes
end Zigzag.Shuffle
```

### `FiniteLinearExtension.lean`

```lean
import PosetShufflePacket
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

namespace Zigzag

/-- Existence on the literal position-to-vertex representation, including the
empty type. The auxiliary linear order is used only to construct the word. -/
theorem finite_linear_extension (α : Type) [Fintype α]
    (R : α → α → Prop) [IsStrictOrder α R] :
    Nonempty {w : Fin (Fintype.card α) ≃ α //
      ∀ a b, R a b → w.symm a < w.symm b} := by
  classical
  let : PartialOrder α := partialOrderOfSO R
  let : Fintype (LinearExtension α) := inferInstanceAs (Fintype α)
  let e := monoEquivOfFin (LinearExtension α) rfl
  let w : Fin (Fintype.card α) ≃ α := e.toEquiv
  refine ⟨⟨w, ?_⟩⟩
  intro a b hab
  have hne : a ≠ b := fun h => by subst b; exact irrefl a hab
  have hle : (toLinearExtension a : LinearExtension α) ≤ toLinearExtension b :=
    toLinearExtension.monotone (show a ≤ b from Or.inr hab)
  exact e.symm.strictMono (lt_of_le_of_ne hle hne)

/-- Empty components cause no nonemptiness gap in the shuffle kernel. -/
theorem componentLE_nonempty {r k : ℕ} (R : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) R] (c : Fin r → Fin k) (j : Fin k) :
    Nonempty (ComponentLE R c j) := by
  let T := {v : Fin r // c v = j}
  let R' : T → T → Prop := fun a b => R a.val b.val
  let : IsStrictOrder T R' :=
    { irrefl := fun a => irrefl a.val
      trans := fun _ _ _ h₁ h₂ => _root_.trans h₁ h₂ }
  exact finite_linear_extension T R'

#print axioms finite_linear_extension
#print axioms componentLE_nonempty
end Zigzag
```

### `ShuffleWordAction.lean`

```lean
import ShuffleCoordinates
import ShuffleProjection
import FiniteLinearExtension

namespace Zigzag.PosetShuffle
open Equiv
variable {r k : ℕ} (c : Fin r → Fin k)

/-- The position action preserves each prescribed component multiplicity. -/
def precomposeFiber (s : Word c) (p : Perm (Fin r)) (j : Fin k) :
    Fiber (s.val ∘ p.symm) j ≃ Fiber s.val j where
  toFun a := ⟨p.symm a.val, a.property⟩
  invFun a := ⟨p a.val, by simpa using a.property⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp

def positionWord (p : Perm (Fin r)) (s : Word c) : Word c :=
  ⟨s.val ∘ p.symm, fun j => (Fintype.card_congr (precomposeFiber c s p j)).trans
    (s.property j)⟩

def positionPerm (p : Perm (Fin r)) : Perm (Word c) where
  toFun := positionWord c p
  invFun := positionWord c p.symm
  left_inv s := by apply Subtype.ext; funext a; simp [positionWord]
  right_inv s := by apply Subtype.ext; funext a; simp [positionWord]

def positions : Perm (Fin r) →* Perm (Word c) where
  toFun := positionPerm c
  map_one' := by apply Equiv.ext; intro s; rfl
  map_mul' p q := by apply Equiv.ext; intro s; rfl

@[simp] theorem positions_apply (p : Perm (Fin r)) (s : Word c) (a : Fin r) :
    (positions c p s).val a = s.val (p.symm a) := rfl

variable (R : Fin r → Fin r → Prop) [DecidableRel R]

/-- For a genuine BK move, component labels undergo the unconditional adjacent
position interchange. Comparability can prevent a swap only within a component. -/
theorem labels_move (hc : ∀ a b, R a b → c a = c b)
    (i : ℕ) (hi : i + 1 < r) (w : LinearExtensions R) :
    labels c (move R i hi w).val = positions c (adjacentSwap i hi) (labels c w.val) := by
  apply Subtype.ext
  funext a
  simp only [labels, Function.comp_apply]
  rw [move_apply]
  by_cases h : incomparable R i hi w.val
  · simp only [h, ite_true]
    rfl
  · simp only [h, ite_false]
    have he : c (w.val (leftPos i hi)) = c (w.val (rightPos i hi)) := by
      unfold incomparable at h
      by_cases hab : R (w.val (leftPos i hi)) (w.val (rightPos i hi))
      · exact hc _ _ hab
      · exact (hc _ _ (not_not.mp (fun hba => h ⟨hab, hba⟩))).symm
    change c (w.val a) = c (w.val (adjacentSwap i hi a))
    simp only [adjacentSwap, Equiv.swap_apply_def]
    split_ifs with ha hb
    · simpa only [ha] using he
    · simpa only [hb] using he.symm
    · rfl

/-- Every transported BK element has a shuffle permutation in the image of the
full position symmetric group. This proves all quotient fields of the packet. -/
theorem transported_projects [IsStrictOrder (Fin r) R]
    (hc : ∀ a b, R a b → c a = c b) :
    transportedBK R c (encode R hc) ≤ Shuffle.projectingSubgroup (positions c) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, hi, rfl⟩
  refine ⟨⟨positions c (adjacentSwap i hi), ⟨adjacentSwap i hi, rfl⟩⟩, ?_⟩
  intro u
  change (encode R hc (move R i hi ((encode R hc).symm u))).1 = _
  change labels c (move R i hi ((encode R hc).symm u)).val = _
  rw [labels_move c R hc]
  have hu := congrArg Prod.fst ((encode R hc).apply_symm_apply u)
  change labels c ((encode R hc).symm u).val = u.1 at hu
  rw [hu]

noncomputable def shuffleProjection [IsStrictOrder (Fin r) R]
    (hc : ∀ a b, R a b → c a = c b) :
    transportedBK R c (encode R hc) →* (positions c).range := by
  letI := componentLE_nonempty R c
  exact Shuffle.subgroupProject (positions c) _ (transported_projects c R hc)

theorem shuffleProjection_fixes [IsStrictOrder (Fin r) R]
    (hc : ∀ a b, R a b → c a = c b)
    (g : (shuffleProjection c R hc).ker)
    (u : Shuffle.State (Word c) (ComponentLE R c)) : (g.val.val u).1 = u.1 := by
  let := componentLE_nonempty R c
  exact Shuffle.subgroupProject_fixes (positions c) _ (transported_projects c R hc) g u

#print axioms labels_move
#print axioms transported_projects
#print axioms shuffleProjection
#print axioms shuffleProjection_fixes
end Zigzag.PosetShuffle
```

### `ShuffleLocality.lean`

```lean
import ShuffleKernel

namespace Zigzag.Shuffle
open Equiv
variable {Sh J : Type*} {X : J → Type*} [∀ j, Nonempty (X j)]

/-- An involutive action is skew once each output coordinate depends only on
its own input coordinate and the shuffle. This avoids picking internal words
in the statement of the poset-locality argument. -/
theorem skew_of_locality (g : Perm (State Sh X)) (τ : Perm Sh)
    (hg : Function.Involutive g) (hτ : Function.Involutive τ)
    (hfirst : ∀ s x, (g (s, x)).1 = τ s)
    (hlocal : ∀ s j x y, x j = y j → (g (s, x)).2 j = (g (s, y)).2 j) :
    Skew g := by
  classical
  let base : ∀ j, X j := fun j => Classical.choice (inferInstance : Nonempty (X j))
  let f : ∀ s : Sh, ∀ j, X j → X j := fun s j a =>
    (g (s, Function.update base j a)).2 j
  have hf : ∀ s x j, (g (s, x)).2 j = f s j (x j) := by
    intro s x j
    exact hlocal s j x _ (Function.update_self j (x j) base).symm
  have hform : ∀ s x, g (s, x) = (τ s, fun j => f s j (x j)) := by
    intro s x
    apply Prod.ext (hfirst s x)
    funext j
    exact hf s x j
  have hinv : ∀ s j a, f (τ s) j (f s j a) = a := by
    intro s j a
    have h := congrArg (fun u : State Sh X => u.2 j)
      (hg (s, Function.update base j a))
    rw [hform, hform] at h
    simpa only [Function.update_self] using h
  let fperm : Coordinates Sh X := fun s j =>
    { toFun := f s j
      invFun := f (τ s) j
      left_inv := hinv s j
      right_inv := fun a => by simpa only [hτ s] using hinv (τ s) j a }
  exact ⟨τ, fperm, hform⟩

#print axioms skew_of_locality
end Zigzag.Shuffle
```

### `ShuffleMoveLocality.lean`

```lean
import ShuffleWordAction
import ShuffleLocality

namespace Zigzag.PosetShuffle
open Equiv
variable {r k : ℕ} {c : Fin r → Fin k}

/-- Equal internal extensions and equal shuffles give equal letters at every
position belonging to that component. -/
theorem values_of_internal (w v : Perm (Fin r)) (j : Fin k)
    (hs : labels c w = labels c v) (hx : internal c w j = internal c v j)
    (a : Fin r) (ha : c (w a) = j) : w a = v a := by
  let p : Fiber (labels c w).val j := ⟨a, ha⟩
  let b := (occurrence c (labels c w) j).symm p
  have h := congrArg (fun e : Fin (Fintype.card (Fiber c j)) ≃ Fiber c j => (e b).val) hx
  simp only [internal_apply] at h
  rw [← hs] at h
  simpa only [b, OrderIso.apply_symm_apply] using h

/-- Conversely the internal word is determined by the letters on its fiber. -/
theorem internal_of_values (w v : Perm (Fin r)) (j : Fin k)
    (hs : labels c w = labels c v)
    (hv : ∀ a, c (w a) = j → w a = v a) : internal c w j = internal c v j := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  simp only [internal_apply]
  rw [← hs]
  exact hv _ (occurrence c (labels c w) j b).property

variable (R : Fin r → Fin r → Prop) [DecidableRel R]

/-- If a BK move fixes a word, the two letters have the same component. -/
theorem same_label_of_not_incomparable (hc : ∀ a b, R a b → c a = c b)
    (i : ℕ) (hi : i + 1 < r) (w : LinearExtensions R)
    (h : ¬ incomparable R i hi w.val) :
    c (w.val (leftPos i hi)) = c (w.val (rightPos i hi)) := by
  unfold incomparable at h
  by_cases hab : R (w.val (leftPos i hi)) (w.val (rightPos i hi))
  · exact hc _ _ hab
  · exact (hc _ _ (not_not.mp (fun hba => h ⟨hab, hba⟩))).symm

omit [DecidableRel R] in
/-- When the local letters are equal, the incomparability decision agrees. -/
theorem incomparable_congr (i : ℕ) (hi : i + 1 < r) (w v : Perm (Fin r))
    (hl : w (leftPos i hi) = v (leftPos i hi))
    (hr : w (rightPos i hi) = v (rightPos i hi)) :
    incomparable R i hi w ↔ incomparable R i hi v := by
  simp only [incomparable, hl, hr]

/-- The asymmetric case needed for locality: if one move swaps and the other
fixes, the moves still agree on the chosen component. -/
theorem move_values_mixed (hc : ∀ a b, R a b → c a = c b)
    (i : ℕ) (hi : i + 1 < r) (w v : LinearExtensions R) (j : Fin k)
    (hs : labels c w.val = labels c v.val)
    (hx : internal c w.val j = internal c v.val j)
    (hw : incomparable R i hi w.val) (hv : ¬ incomparable R i hi v.val)
    (a : Fin r) (ha : c ((move R i hi w).val a) = j) :
    (move R i hi w).val a = (move R i hi v).val a := by
  have hlabels : ∀ p, c (w.val p) = c (v.val p) :=
    fun p => congrArg (fun s : Word c => s.val p) hs
  have he := same_label_of_not_incomparable R hc i hi v hv
  have hne : leftPos i hi ≠ rightPos i hi := by
    intro h
    have := congrArg Fin.val h
    simp only [leftPos, rightPos] at this
    omega
  rw [move_apply, ite_eq_left hw] at ha
  rw [move_apply, ite_eq_left hw, move_apply, ite_eq_right hv]
  change w.val (adjacentSwap i hi a) = v.val a
  change c (w.val (adjacentSwap i hi a)) = j at ha
  by_cases hl : a = leftPos i hi
  · have hjr : c (w.val (rightPos i hi)) = j := by simpa [hl, adjacentSwap] using ha
    have hjl : c (w.val (leftPos i hi)) = j := by
      rw [hlabels, he, ← hlabels]; exact hjr
    have hwl := values_of_internal w.val v.val j hs hx _ hjl
    have hwr := values_of_internal w.val v.val j hs hx _ hjr
    exact False.elim (hv ((incomparable_congr R i hi w.val v.val hwl hwr).mp hw))
  · by_cases hr : a = rightPos i hi
    · have hjl : c (w.val (leftPos i hi)) = j := by simpa [hr, adjacentSwap] using ha
      have hjr : c (w.val (rightPos i hi)) = j := by
        rw [hlabels, ← he, ← hlabels]; exact hjl
      have hwl := values_of_internal w.val v.val j hs hx _ hjl
      have hwr := values_of_internal w.val v.val j hs hx _ hjr
      exact False.elim (hv ((incomparable_congr R i hi w.val v.val hwl hwr).mp hw))
    · have hp : adjacentSwap i hi a = a := by
        simp [adjacentSwap, Equiv.swap_apply_def, hl, hr]
      rw [hp] at ha ⊢
      exact values_of_internal w.val v.val j hs hx a ha

/-- Each output internal extension depends only on its own input extension
and the common shuffle, even though other components may move simultaneously. -/
theorem internal_move_local (hc : ∀ a b, R a b → c a = c b)
    (i : ℕ) (hi : i + 1 < r) (w v : LinearExtensions R) (j : Fin k)
    (hs : labels c w.val = labels c v.val)
    (hx : internal c w.val j = internal c v.val j) :
    internal c (move R i hi w).val j = internal c (move R i hi v).val j := by
  have hout : labels c (move R i hi w).val = labels c (move R i hi v).val := by
    rw [labels_move c R hc, labels_move c R hc, hs]
  apply internal_of_values _ _ j hout
  intro a ha
  by_cases hw : incomparable R i hi w.val
  · by_cases hv : incomparable R i hi v.val
    · rw [move_apply, ite_eq_left hw] at ha
      rw [move_apply, ite_eq_left hw, move_apply, ite_eq_left hv]
      exact values_of_internal w.val v.val j hs hx _ ha
    · exact move_values_mixed R hc i hi w v j hs hx hw hv a ha
  · by_cases hv : incomparable R i hi v.val
    · have ha' : c ((move R i hi v).val a) = j :=
        (congrArg (fun s : Word c => s.val a) hout).symm.trans ha
      exact (move_values_mixed R hc i hi v w j hs.symm hx.symm hv hw a ha').symm
    · rw [move_apply, ite_eq_right hw] at ha
      rw [move_apply, ite_eq_right hw, move_apply, ite_eq_right hv]
      exact values_of_internal w.val v.val j hs hx a ha

#print axioms internal_move_local
end Zigzag.PosetShuffle
```

### `ShufflePacketConstruction.lean`

```lean
import ShuffleMoveLocality

namespace Zigzag.PosetShuffle
open Equiv
variable {r k : ℕ} (R : Fin r → Fin r → Prop) [DecidableRel R]
variable [IsStrictOrder (Fin r) R] {c : Fin r → Fin k}
variable (hc : ∀ a b, R a b → c a = c b)

omit [DecidableRel R] [IsStrictOrder (Fin r) R] in
@[simp] theorem encode_symm_labels (u : Shuffle.State (Word c) (ComponentLE R c)) :
    labels c ((encode R hc).symm u).val = u.1 :=
  congrArg Prod.fst ((encode R hc).apply_symm_apply u)

omit [DecidableRel R] [IsStrictOrder (Fin r) R] in
@[simp] theorem encode_symm_internal (u : Shuffle.State (Word c) (ComponentLE R c))
    (j : Fin k) : internal c ((encode R hc).symm u).val j = (u.2 j).val :=
  congrArg (fun v : Shuffle.State (Word c) (ComponentLE R c) => (v.2 j).val)
    ((encode R hc).apply_symm_apply u)

/-- The transported literal adjacent BK involution is skew. -/
theorem generator_skew (i : ℕ) (hi : i + 1 < r) :
    Shuffle.Skew ((encode R hc).permCongrHom (move R i hi)) := by
  let := componentLE_nonempty R c
  let e := encode R hc
  apply Shuffle.skew_of_locality _ (positions c (adjacentSwap i hi))
  · intro u
    change e (move R i hi (e.symm (e (move R i hi (e.symm u)))) ) = u
    rw [Equiv.symm_apply_apply, move_involutive R i hi, Equiv.apply_symm_apply]
  · intro s
    apply Subtype.ext
    funext a
    simp [positions_apply, adjacentSwap]
  · intro s x
    change labels c (move R i hi (e.symm (s, x))).val = _
    rw [labels_move c R hc, encode_symm_labels]
  · intro s j x y hxy
    apply Subtype.ext
    change internal c (move R i hi (e.symm (s, x))).val j =
      internal c (move R i hi (e.symm (s, y))).val j
    apply internal_move_local R hc i hi _ _ j
    · simp only [e, encode_symm_labels]
    · simp only [e, encode_symm_internal, hxy]

theorem transported_skew :
    ∀ g : transportedBK R c (encode R hc), Shuffle.Skew g.val := by
  have hle : transportedBK R c (encode R hc) ≤ Shuffle.skewSubgroup _ _ := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, hi, rfl⟩
    exact generator_skew R hc i hi
  exact fun g => hle g.property

/-- All fields are proved, including the quotient image of the full position
symmetric group. Empty components are permitted. -/
noncomputable def packet : PosetShufflePacket R c where
  Sh := Word c
  finiteSh := inferInstance
  nonemptyComponents := componentLE_nonempty R c
  encode := encode R hc
  B := (positions c).range
  groupB := inferInstance
  projection := shuffleProjection c R hc
  positions := (positions c).rangeRestrict
  positions_surjective := (positions c).rangeRestrict_surjective
  skew := transported_skew R hc
  fixes := shuffleProjection_fixes c R hc

end PosetShuffle

/-- The first of the three stage-1 missing hypotheses is discharged. -/
theorem shuffle_packets_exist : ShufflePacketsExist := by
  intro r k R _ _ c hc
  exact ⟨PosetShuffle.packet R hc⟩

/-- The complete residual-poset simple-section bound, without a packet
existence hypothesis. This applies to arbitrary component partitions. -/
theorem leftover_section_bound : LeftoverSectionBound :=
  leftover_bound_of_packets shuffle_packets_exist

#print axioms PosetShuffle.generator_skew
#print axioms PosetShuffle.packet
#print axioms shuffle_packets_exist
#print axioms leftover_section_bound
end Zigzag
```

### `FenceResidualConnectivity.lean`

```lean
import FenceGeometry
import Mathlib.Logic.Relation

namespace Zigzag

abbrev Residue {n : ℕ} (a b : Fin n) := {v : Fin n // v ≠ a ∧ v ≠ b}

def ResidualAdjacent {n : ℕ} {a b : Fin n} (x y : Residue a b) : Prop :=
  zigLt n x.val y.val ∨ zigLt n y.val x.val

def ResidualConnected {n : ℕ} (a b : Fin n) : Prop :=
  ∀ x y : Residue a b, Relation.ReflTransGen ResidualAdjacent x y

/-- A path in a residue cannot cross either of the deleted vertices. -/
theorem residual_path_side {n : ℕ} {a b : Fin n} {x y : Residue a b}
    (h : Relation.ReflTransGen ResidualAdjacent x y) (z : Fin n)
    (hz : z = a ∨ z = b) : x.val < z ↔ y.val < z := by
  induction h with
  | refl => rfl
  | @tail v w hp he ih =>
    apply ih.trans
    have hadj := (zigLt_comparable_iff n v.val w.val).mp he
    have hv : v.val ≠ z := by rcases hz with rfl | rfl; exact v.property.1; exact v.property.2
    have hw : w.val ≠ z := by rcases hz with rfl | rfl; exact w.property.1; exact w.property.2
    have hv' : v.val.val ≠ z.val := fun he => hv (Fin.ext he)
    have hw' : w.val.val ≠ z.val := fun he => hw (Fin.ext he)
    simp only [Fin.lt_def]
    omega

theorem residual_connected_interval {n : ℕ} (a b : Fin n)
    (h : ResidualConnected a b) : ResidualInterval n a b := by
  intro x y z hxa hxb hya hyb hxz hzy
  have hp := h ⟨x, hxa, hxb⟩ ⟨y, hya, hyb⟩
  constructor
  · intro he
    have hs := residual_path_side hp z (Or.inl he)
    have hxne : x.val ≠ z.val := fun hv => hxa ((Fin.ext hv).trans he)
    have hyne : y.val ≠ z.val := fun hv => hya ((Fin.ext hv).trans he)
    simp only [Fin.lt_def, Fin.le_def] at hs hxz hzy
    change x.val < z.val ↔ y.val < z.val at hs
    omega
  · intro he
    have hs := residual_path_side hp z (Or.inr he)
    have hxne : x.val ≠ z.val := fun hv => hxb ((Fin.ext hv).trans he)
    have hyne : y.val ≠ z.val := fun hv => hyb ((Fin.ext hv).trans he)
    change x.val < z.val ↔ y.val < z.val at hs
    simp only [Fin.le_def] at hxz hzy
    omega

/-- Every increasing segment in an interval residue is a path in the literal
comparability graph of the height-two fence. -/
theorem residual_interval_walk {n : ℕ} {a b : Fin n} (h : ResidualInterval n a b)
    (x y : Residue a b) (hxy : x.val ≤ y.val) :
    Relation.ReflTransGen ResidualAdjacent x y := by
  have step : ∀ d (z : Residue a b), z.val.val = x.val.val + d → z.val ≤ y.val →
      Relation.ReflTransGen ResidualAdjacent x z := by
    intro d
    induction d with
    | zero =>
      intro z hz _
      have he : x = z := Subtype.ext (Fin.ext (by omega))
      subst z
      exact .refl
    | succ d ih =>
      intro z hz hzy
      have hprev : z.val.val - 1 < n := by have := z.val.isLt; omega
      let p : Fin n := ⟨z.val.val - 1, hprev⟩
      have hxp : x.val ≤ p := by change x.val.val ≤ z.val.val - 1; omega
      have hpy : p ≤ y.val := by change z.val.val - 1 ≤ y.val.val; have := hzy; omega
      let v : Residue a b := ⟨p, h x.val y.val p x.property.1 x.property.2
        y.property.1 y.property.2 hxp hpy⟩
      have hv : v.val.val = x.val.val + d := by change z.val.val - 1 = _; omega
      have hp := ih v hv hpy
      apply hp.tail
      apply (zigLt_comparable_iff n v.val z.val).mpr
      left
      change z.val.val - 1 + 1 = z.val.val
      omega
  exact step (y.val.val - x.val.val) y (by have := hxy; omega) le_rfl

theorem residual_interval_connected {n : ℕ} (a b : Fin n)
    (h : ResidualInterval n a b) : ResidualConnected a b := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact residual_interval_walk h x y hxy
  · have hp := residual_interval_walk h y x hyx
    clear hyx
    induction hp with
    | refl => exact .refl
    | @tail v w _ he ih =>
      exact ih.head (Or.symm he)

/-- Literal connectivity classification of the residual comparability graph. -/
theorem residual_connected_endpoints {n : ℕ} (hn : 6 ≤ n) (heven : Even n)
    (a b : Fin n) (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) :
    ResidualConnected a b ↔
      (a.val = 0 ∧ b.val = 1) ∨ (a.val = 0 ∧ b.val = n - 1) ∨
        (a.val = n - 2 ∧ b.val = n - 1) :=
  (show ResidualConnected a b ↔ ResidualInterval n a b from
    ⟨residual_connected_interval a b, residual_interval_connected a b⟩).trans
      (residual_interval_endpoints hn heven a b ha hb)

#print axioms residual_connected_endpoints
end Zigzag
```

### `ContinuationAudit.lean`

```lean
import Audit
import ShufflePacketConstruction
import FenceResidualConnectivity
import FenceResidueMaps
import FenceEndpointAction

set_option pp.universes false

#eval Lean.versionString
#check Zigzag.PosetShuffle.encode
#check Zigzag.finite_linear_extension
#check Zigzag.componentLE_nonempty
#check Zigzag.PosetShuffle.labels_move
#check Zigzag.PosetShuffle.internal_move_local
#check Zigzag.shuffle_packets_exist
#check Zigzag.leftover_section_bound
#check Zigzag.first_vertex_even
#check Zigzag.last_vertex_odd
#check Zigzag.residual_connected_endpoints
#check Zigzag.residueA_relIso
#check Zigzag.residueB_relIso
#check Zigzag.residueC_relIso
#check Zigzag.endpointA
#check Zigzag.endpointA_injective
#check Zigzag.bk_endpointA
#print Zigzag.AlternatingStep
#print Zigzag.OddStep
#print Zigzag.LeftoverSectionBound
#check Zigzag.even_zigzag_LE_symmetric_from_steps

#print axioms Zigzag.card_zigzagLE_four
#print axioms Zigzag.card_zigzagLE_six
#print axioms Zigzag.zero_symmetric
#print axioms Zigzag.two_symmetric
#print axioms Zigzag.four_symmetric
#print axioms Zigzag.shuffle_packets_exist
#print axioms Zigzag.leftover_section_bound
#print axioms Zigzag.residual_connected_endpoints
#print axioms Zigzag.residueA_relIso
#print axioms Zigzag.residueB_relIso
#print axioms Zigzag.residueC_relIso
#print axioms Zigzag.endpointA_injective
#print axioms Zigzag.bk_endpointA
#print axioms Zigzag.even_zigzag_LE_symmetric_from_steps
```

### `FenceCountSuccessor.lean`

```lean
import FenceCountGrowth
import FiniteLinearExtension

namespace Zigzag
open Equiv

/-- Add a new final maximal vertex at the final position. -/
def appendWord {n : ℕ} (w : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans ((optionCongr w).trans finSuccEquivLast.symm)

@[simp] theorem appendWord_last {n : ℕ} (w : Perm (Fin n)) :
    appendWord w (Fin.last n) = Fin.last n := by
  simp [appendWord]
@[simp] theorem appendWord_old {n : ℕ} (w : Perm (Fin n)) (a : Fin n) :
    appendWord w a.castSucc = (w a).castSucc := by
  simp [appendWord]
@[simp] theorem appendWord_symm_last {n : ℕ} (w : Perm (Fin n)) :
    (appendWord w).symm (Fin.last n) = Fin.last n :=
  (appendWord w).symm_apply_eq.mpr (appendWord_last w).symm
@[simp] theorem appendWord_symm_old {n : ℕ} (w : Perm (Fin n)) (a : Fin n) :
    (appendWord w).symm a.castSucc = (w.symm a).castSucc := by
  apply (appendWord w).symm_apply_eq.mpr
  simp

theorem appendWord_isLE {n : ℕ} (hn : Odd n) (w : ZigzagLE n) :
    IsLE (zigLt (n + 1)) (appendWord w.val) := by
  have hnmod : n % 2 = 1 := by obtain ⟨k, hk⟩ := hn; omega
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    have ha := hab.1
    change n % 2 = 0 at ha
    omega
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      simp only [appendWord_symm_old, appendWord_symm_last]
      exact (w.val.symm a).isLt
    | cast b =>
      have hh := w.property a b hab
      simpa only [appendWord_symm_old, Fin.castSucc_lt_castSucc_iff] using hh

def appendExtension {n : ℕ} (hn : Odd n) (w : ZigzagLE n) : ZigzagLE (n + 1) :=
  ⟨appendWord w.val, appendWord_isLE hn w⟩

theorem appendExtension_injective {n : ℕ} (hn : Odd n) :
    Function.Injective (appendExtension hn) := by
  intro w v he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have hh := congrArg (fun u : ZigzagLE (n + 1) => u.val a.castSucc) he
  simpa only [appendExtension, appendWord_old, Fin.castSucc_inj] using hh

/-- Add a new final minimal vertex at the first position. -/
def prependWord {n : ℕ} (w : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  (finSuccEquiv n).trans ((optionCongr w).trans finSuccEquivLast.symm)

@[simp] theorem prependWord_first {n : ℕ} (w : Perm (Fin n)) :
    prependWord w 0 = Fin.last n := by
  simp [prependWord]
@[simp] theorem prependWord_old {n : ℕ} (w : Perm (Fin n)) (a : Fin n) :
    prependWord w a.succ = (w a).castSucc := by
  simp [prependWord]
@[simp] theorem prependWord_symm_last {n : ℕ} (w : Perm (Fin n)) :
    (prependWord w).symm (Fin.last n) = 0 :=
  (prependWord w).symm_apply_eq.mpr (prependWord_first w).symm
@[simp] theorem prependWord_symm_old {n : ℕ} (w : Perm (Fin n)) (a : Fin n) :
    (prependWord w).symm a.castSucc = (w.symm a).succ := by
  apply (prependWord w).symm_apply_eq.mpr
  simp

theorem prependWord_isLE {n : ℕ} (hn : Even n) (w : ZigzagLE n) :
    IsLE (zigLt (n + 1)) (prependWord w.val) := by
  have hnmod : n % 2 = 0 := by obtain ⟨k, hk⟩ := hn; omega
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    have ha := hab.1
    have hb := hab.2
    have haBound := a.isLt
    change a.val % 2 = 0 at ha
    change n = a.val + 1 ∨ a.val = n + 1 at hb
    omega
  | cast b =>
    induction a using Fin.lastCases with
    | last =>
      simp only [prependWord_symm_last, prependWord_symm_old]
      change 0 < (w.val.symm b).val + 1
      omega
    | cast a =>
      have hh := w.property a b hab
      simpa only [prependWord_symm_old, Fin.succ_lt_succ_iff] using hh

def prependExtension {n : ℕ} (hn : Even n) (w : ZigzagLE n) : ZigzagLE (n + 1) :=
  ⟨prependWord w.val, prependWord_isLE hn w⟩

theorem prependExtension_injective {n : ℕ} (hn : Even n) :
    Function.Injective (prependExtension hn) := by
  intro w v he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have hh := congrArg (fun u : ZigzagLE (n + 1) => u.val a.succ) he
  simpa only [prependExtension, prependWord_old, Fin.castSucc_inj] using hh

/-- The actual fence extension count is monotone at every successor, in both
parities; no numerical recurrence is used. -/
theorem card_mono_succ (n : ℕ) :
    Fintype.card (ZigzagLE n) ≤ Fintype.card (ZigzagLE (n + 1)) := by
  rcases Nat.even_or_odd n with hn | hn
  · exact Fintype.card_le_of_injective _ (prependExtension_injective hn)
  · exact Fintype.card_le_of_injective _ (appendExtension_injective hn)

theorem card_mono {m n : ℕ} (h : m ≤ n) :
    Fintype.card (ZigzagLE m) ≤ Fintype.card (ZigzagLE n) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (card_mono_succ n)

/-- The old final endpoint is minimal in an odd fence of order at least three,
so it cannot be the final letter of an extension. -/
theorem odd_last_not_endpoint {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (w : ZigzagLE n) :
    (w.val ((⟨n - 1, by omega⟩ : Fin n))).val ≠ n - 1 := by
  intro he
  have hnmod : n % 2 = 1 := by obtain ⟨k, hk⟩ := hn; omega
  let a : Fin n := ⟨n - 1, by omega⟩
  let b : Fin n := ⟨n - 2, by omega⟩
  have hab : zigLt n a b := by dsimp [zigLt, a, b]; omega
  have hh := w.property a b hab
  have ha : w.val.symm a = (⟨n - 1, by omega⟩ : Fin n) := by
    apply w.val.symm_apply_eq.mpr
    exact Fin.ext he.symm
  rw [ha] at hh
  have hb := (w.val.symm b).isLt
  change n - 1 < (w.val.symm b).val at hh
  omega

#print axioms card_mono_succ
#print axioms card_mono
#print axioms odd_last_not_endpoint
end Zigzag
```

### `FenceCountSeparation.lean`

```lean
import FenceCountSuccessor

namespace Zigzag
open Equiv

theorem append_last_incomparable {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (w : ZigzagLE n) :
    incomparable (zigLt (n + 1)) (n - 1) (by omega) (appendExtension hn w).val := by
  let a : Fin n := ⟨n - 1, by omega⟩
  have hl : leftPos (n - 1) (by omega : n - 1 + 1 < n + 1) = a.castSucc := by
    ext; rfl
  have hr : rightPos (n - 1) (by omega : n - 1 + 1 < n + 1) = Fin.last n := by
    ext; dsimp [rightPos]; omega
  have hw := odd_last_not_endpoint hn h3 w
  have hp := (w.val a).isLt
  have hnmod : n % 2 = 1 := by obtain ⟨k, hk⟩ := hn; omega
  change _ ∧ _
  simp only [hl, hr, appendExtension, appendWord_old, appendWord_last]
  constructor
  · intro h
    have hh := h.2
    change n = (w.val a).val + 1 ∨ (w.val a).val = n + 1 at hh
    exact hw (by change (w.val a).val = n - 1; omega)
  · intro h
    have hh := h.1
    change n % 2 = 0 at hh
    omega

theorem bk_append_last {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (w : ZigzagLE n) :
    (bk (n + 1) (n - 1) (by omega) (appendExtension hn w)).val (Fin.last n) =
      (w.val ⟨n - 1, by omega⟩).castSucc := by
  let a : Fin n := ⟨n - 1, by omega⟩
  have hl : leftPos (n - 1) (by omega : n - 1 + 1 < n + 1) = a.castSucc := by
    ext; rfl
  have hr : rightPos (n - 1) (by omega : n - 1 + 1 < n + 1) = Fin.last n := by
    ext; dsimp [rightPos]; omega
  have hs : adjacentSwap (n - 1) (by omega : n - 1 + 1 < n + 1) (Fin.last n) = a.castSucc := by
    rw [adjacentSwap, hl, hr]
    exact Equiv.swap_apply_right _ _
  have hv := move_apply (zigLt (n + 1)) (n - 1) (by omega) (appendExtension hn w)
  simp only [append_last_incomparable hn h3 w, ite_true] at hv
  have hh := congrArg (fun e : Perm (Fin (n + 1)) => e (Fin.last n)) hv
  simpa only [bk, rawSwap, Equiv.trans_apply, hs, appendExtension, appendWord_old] using hh

/-- Strict growth from each odd order at least three to the next even order.
One extension outside the append image is enough, so the stronger two-copy
insertion estimate from the ordinary proof is unnecessary. -/
theorem card_strict_odd_succ {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    Fintype.card (ZigzagLE n) < Fintype.card (ZigzagLE (n + 1)) := by
  have hw : Nonempty (ZigzagLE n) := by
    have hh := finite_linear_extension (Fin n) (zigLt n)
    rw [Fintype.card_fin] at hh
    exact hh
  obtain ⟨w⟩ := hw
  let v := bk (n + 1) (n - 1) (by omega) (appendExtension hn w)
  apply Fintype.card_lt_of_injective_of_notMem (appendExtension hn) (appendExtension_injective hn) (b := v)
  rintro ⟨u, hu⟩
  have hh := congrArg (fun x : ZigzagLE (n + 1) => (x.val (Fin.last n)).val) hu
  have he : v.val (Fin.last n) = (w.val ⟨n - 1, by omega⟩).castSucc := bk_append_last hn h3 w
  have huend : (appendExtension hn u).val (Fin.last n) = Fin.last n := appendWord_last u.val
  rw [huend, he] at hh
  have := (w.val ⟨n - 1, by omega⟩).isLt
  change n = (w.val ⟨n - 1, by omega⟩).val at hh
  omega

theorem card_previous_lt {r : ℕ} (hr : Even r) (h4 : 4 ≤ r) :
    Fintype.card (ZigzagLE (r - 1)) < Fintype.card (ZigzagLE r) := by
  have ho : Odd (r - 1) := by
    obtain ⟨k, hk⟩ := hr
    exact ⟨k - 1, by omega⟩
  have hh := card_strict_odd_succ ho (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hh

/-- The precise cardinal bound needed for every strictly smaller residual
component, once its fence/dual-fence equivalence has been proved. -/
theorem card_smaller_lt {j r : ℕ} (hr : Even r) (h4 : 4 ≤ r) (hj : j < r) :
    Fintype.card (ZigzagLE j) < Fintype.card (ZigzagLE r) :=
  (card_mono (show j ≤ r - 1 by omega)).trans_lt (card_previous_lt hr h4)

#print axioms card_strict_odd_succ
#print axioms card_previous_lt
#print axioms card_smaller_lt
end Zigzag
```

### `FenceSectionArithmetic.lean`

```lean
import FenceCountSeparation
import FenceDiagonalIsolation
import ShufflePacketConstruction
import Mathlib.Tactic.Linarith

namespace Zigzag

/-- A factorial at a strictly smaller argument than d is less than d!/2
when d ≥ 5. Avoids division by using the exact alternating-group order. -/
theorem factorial_lt_half {m d a : ℕ} (h5 : 5 ≤ d) (hmd : m < d)
    (ha : 2 * a = d.factorial) : m.factorial < a := by
  have hd : d = (d - 1) + 1 := by omega
  have hf : d.factorial = d * (d - 1).factorial := by
    calc
      d.factorial = (d - 1 + 1).factorial := congrArg Nat.factorial hd
      _ = (d - 1 + 1) * (d - 1).factorial := Nat.factorial_succ _
      _ = d * (d - 1).factorial := congrArg (fun k => k * (d - 1).factorial) hd.symm
  have hm := Nat.factorial_le (show m ≤ d - 1 by omega)
  have hp := Nat.factorial_pos (d - 1)
  nlinarith

theorem factorial_lt_alternating_card {r m : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (hm : m < Fintype.card (ZigzagLE r)) :
    m.factorial < Nat.card (alternatingGroup (ZigzagLE r)) := by
  have h5 := five_le_card r hr h4
  let : Nontrivial (ZigzagLE r) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  apply factorial_lt_half h5 hm
  have hh := two_mul_nat_card_alternatingGroup (α := ZigzagLE r)
  rw [Nat.card_perm, Nat.card_eq_fintype_card] at hh
  simpa only [Nat.card_eq_fintype_card] using hh

/-- The entire numerical part of applying the disconnected-poset bound.
Only actual component extension counts below E_r are required. -/
theorem residual_sectionFree_of_component_lt {r k : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (R : Fin r → Fin r → Prop) [DecidableRel R] [IsStrictOrder (Fin r) R]
    (c : Fin r → Fin k) (hc : ∀ a b, R a b → c a = c b)
    (he : ∀ j, Nat.card (ComponentLE R c j) < Fintype.card (ZigzagLE r)) :
    SectionFree (alternatingGroup (ZigzagLE r)) (relationBK R) := by
  let : IsSimpleGroup (alternatingGroup (ZigzagLE r)) :=
    alternatingGroup.isSimpleGroup (by
      simpa only [Nat.card_eq_fintype_card] using five_le_card r hr h4)
  apply leftover_section_bound r k R c hc (alternatingGroup (ZigzagLE r))
  · exact factorial_lt_alternating_card hr h4 (vertices_lt_card r hr h4)
  · intro j
    exact factorial_lt_alternating_card hr h4 (he j)

#print axioms factorial_lt_alternating_card
#print axioms residual_sectionFree_of_component_lt
end Zigzag
```

### `ResidualIntervals.lean`

```lean
import ResidualWordFrames
import FenceResidualConnectivity
import Mathlib.Tactic.FinCases

namespace Zigzag
open Equiv
namespace ResidualFrame
variable {r : ℕ} (F : ResidualFrame r)

def first : Fin (r + 2) := F.vertices.symm none
def last : Fin (r + 2) := F.vertices.symm (some none)
def vertex (x : Fin r) : Fin (r + 2) := F.vertices.symm (some (some x))

theorem first_ne_last : F.first ≠ F.last := by
  intro he
  have := F.vertices.symm.injective he
  cases this

theorem vertex_ne_first (x : Fin r) : F.vertex x ≠ F.first := by
  intro he
  have := F.vertices.symm.injective he
  cases this

theorem vertex_ne_last (x : Fin r) : F.vertex x ≠ F.last := by
  intro he
  have := F.vertices.symm.injective he
  cases this

theorem vertex_injective : Function.Injective F.vertex := by
  intro x y he
  have := F.vertices.symm.injective he
  exact Option.some_injective _ (Option.some_injective _ this)

theorem vertex_surjective (v : Fin (r + 2)) (hf : v ≠ F.first) (hl : v ≠ F.last) :
    ∃ x, F.vertex x = v := by
  obtain ⟨q, rfl⟩ := F.vertices.symm.surjective v
  cases q with
  | none => exact (hf rfl).elim
  | some q =>
    cases q with
    | none => exact (hl rfl).elim
    | some x => exact ⟨x, rfl⟩

def low : ℕ := min F.first.val F.last.val
def high : ℕ := max F.first.val F.last.val

theorem low_lt_high : F.low < F.high := by
  have hne := F.first_ne_last
  have hne' : F.first.val ≠ F.last.val := fun h => hne (Fin.ext h)
  dsimp [low, high]
  omega

theorem high_lt : F.high < r + 2 := by
  have := F.first.isLt
  have := F.last.isLt
  dsimp [high]
  omega

def piece (x : Fin r) : Fin 3 :=
  if (F.vertex x).val < F.low then 0 else if (F.vertex x).val < F.high then 1 else 2

def start : Fin 3 → ℕ := ![0, F.low + 1, F.high + 1]
def length : Fin 3 → ℕ := ![F.low, F.high - F.low - 1, r + 2 - F.high - 1]

theorem vertex_ne_low (x : Fin r) : (F.vertex x).val ≠ F.low := by
  have hf := F.vertex_ne_first x
  have hl := F.vertex_ne_last x
  have hf' : (F.vertex x).val ≠ F.first.val := fun h => hf (Fin.ext h)
  have hl' : (F.vertex x).val ≠ F.last.val := fun h => hl (Fin.ext h)
  dsimp [low]
  omega

theorem vertex_ne_high (x : Fin r) : (F.vertex x).val ≠ F.high := by
  have hf := F.vertex_ne_first x
  have hl := F.vertex_ne_last x
  have hf' : (F.vertex x).val ≠ F.first.val := fun h => hf (Fin.ext h)
  have hl' : (F.vertex x).val ≠ F.last.val := fun h => hl (Fin.ext h)
  dsimp [high]
  omega

theorem start_add_length (j : Fin 3) : F.start j + F.length j ≤ r + 2 := by
  have := F.low_lt_high
  have := F.high_lt
  fin_cases j <;> simp [start, length] <;> omega

theorem piece_iff (x : Fin r) (j : Fin 3) :
    F.piece x = j ↔ F.start j ≤ (F.vertex x).val ∧
      (F.vertex x).val < F.start j + F.length j := by
  have := F.vertex_ne_low x
  have := F.vertex_ne_high x
  have := (F.vertex x).isLt
  have := F.low_lt_high
  have := F.high_lt
  fin_cases j <;> simp [piece, start, length] <;> split_ifs <;> omega

/-- All fence relations remain within one of the three intervals cut by the
two deleted vertices. Empty intervals are allowed. -/
theorem relation_piece (x y : Fin r) (h : F.relation x y) : F.piece x = F.piece y := by
  have hxlo := F.vertex_ne_low x
  have hxhi := F.vertex_ne_high x
  have hylo := F.vertex_ne_low y
  have hyhi := F.vertex_ne_high y
  have hh : (F.vertex y).val = (F.vertex x).val + 1 ∨
      (F.vertex x).val = (F.vertex y).val + 1 := h.2
  simp only [piece]
  split_ifs <;> omega

/-- In a disconnected residue no interval can use all r remaining vertices. -/
theorem length_lt_of_disconnected (hd : ¬ ResidualConnected F.first F.last)
    (j : Fin 3) : F.length j < r := by
  have hlo := F.low_lt_high
  have hhi := F.high_lt
  by_contra h
  have hinterval : ResidualInterval (r + 2) F.first F.last := by
    intro x y z hxf hxl hyf hyl hxz hzy
    have hxf' : x.val ≠ F.first.val := fun he => hxf (Fin.ext he)
    have hxl' : x.val ≠ F.last.val := fun he => hxl (Fin.ext he)
    have hyf' : y.val ≠ F.first.val := fun he => hyf (Fin.ext he)
    have hyl' : y.val ≠ F.last.val := fun he => hyl (Fin.ext he)
    have hx := x.isLt
    have hy := y.isLt
    have hz := z.isLt
    have hf := F.first.isLt
    have hl := F.last.isLt
    have hne : F.first.val ≠ F.last.val := fun he => F.first_ne_last (Fin.ext he)
    change x.val ≤ z.val at hxz
    change z.val ≤ y.val at hzy
    fin_cases j <;> simp [length] at h
    all_goals
      constructor <;> intro he <;> have hz' := congrArg Fin.val he
      all_goals dsimp [low, high] at *; omega
  exact hd (residual_interval_connected F.first F.last hinterval)

#print axioms relation_piece
#print axioms length_lt_of_disconnected
end ResidualFrame
end Zigzag
```

### `ExtensionCardTransport.lean`

```lean
import RemainingStatements
import Mathlib.Data.Fin.Rev

namespace Zigzag
open Equiv

/-- Vertex coordinates preserve literal position-to-vertex extensions; the
position equivalence is only a change along the proved cardinal equality. -/
noncomputable def extensionRelEquiv {α : Type} [Fintype α] {m : ℕ}
    (R : α → α → Prop) (T : Fin m → Fin m → Prop)
    (e : Fin m ≃ α) (he : ∀ a b, R (e a) (e b) ↔ T a b) :
    {w : Fin (Fintype.card α) ≃ α // ∀ a b, R a b → w.symm a < w.symm b} ≃
      LinearExtensions T := by
  have hc : m = Fintype.card α := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  let p : Fin m ≃ Fin (Fintype.card α) := finCongr hc
  refine
    { toFun := fun w => ⟨p.trans (w.val.trans e.symm), ?_⟩
      invFun := fun w => ⟨p.symm.trans (w.val.trans e), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a b hab
    have h := w.property (e a) (e b) ((he a b).mpr hab)
    change (w.val.symm (e a)).val < (w.val.symm (e b)).val at h
    exact h
  · intro a b hab
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h := w.property x y ((he x y).mp hab)
    change (w.val.symm x).val < (w.val.symm y).val at h
    change (w.val.symm (e.symm (e x))).val < (w.val.symm (e.symm (e y))).val
    simpa only [Equiv.symm_apply_apply] using h
  · intro w
    apply Subtype.ext
    ext a
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  · intro w
    apply Subtype.ext
    ext a
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Reversing position order, without relabeling vertices, identifies the
extensions of a relation and of its order dual. -/
def dualExtensionEquiv {m : ℕ} (R : Fin m → Fin m → Prop) :
    LinearExtensions (fun a b => R b a) ≃ LinearExtensions R where
  toFun w := ⟨Fin.revPerm.trans w.val, by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (w.property b a hab)⟩
  invFun w := ⟨Fin.revPerm.trans w.val, by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (w.property b a hab)⟩
  left_inv w := by apply Subtype.ext; ext a; simp
  right_inv w := by apply Subtype.ext; ext a; simp

#print axioms extensionRelEquiv
#print axioms dualExtensionEquiv
end Zigzag
```

### `ResidualComponentCoordinates.lean`

```lean
import ResidualIntervals
import ExtensionCardTransport

namespace Zigzag
open Equiv
namespace ResidualFrame
variable {r : ℕ} (F : ResidualFrame r)

def pieceVertex (j : Fin 3) (x : Fin (F.length j)) : Fin (r + 2) :=
  ⟨F.start j + x.val, by
    have := F.start_add_length j
    have := x.isLt
    omega⟩

theorem pieceVertex_ne_first (j : Fin 3) (x : Fin (F.length j)) :
    F.pieceVertex j x ≠ F.first := by
  intro he
  have hv := congrArg Fin.val he
  have hx := x.isLt
  have hlo := F.low_lt_high
  have hhi := F.high_lt
  change F.start j + x.val = F.first.val at hv
  fin_cases j <;> simp [start, length] at hv hx
  all_goals dsimp [low, high] at *; omega

theorem pieceVertex_ne_last (j : Fin 3) (x : Fin (F.length j)) :
    F.pieceVertex j x ≠ F.last := by
  intro he
  have hv := congrArg Fin.val he
  have hx := x.isLt
  have hlo := F.low_lt_high
  have hhi := F.high_lt
  change F.start j + x.val = F.last.val at hv
  fin_cases j <;> simp [start, length] at hv hx
  all_goals dsimp [low, high] at *; omega

noncomputable def pieceMap (j : Fin 3) (x : Fin (F.length j)) :
    {v : Fin r // F.piece v = j} := by
  let y := (F.vertex_surjective (F.pieceVertex j x)
    (F.pieceVertex_ne_first j x) (F.pieceVertex_ne_last j x)).choose
  have hy : F.vertex y = F.pieceVertex j x :=
    (F.vertex_surjective (F.pieceVertex j x)
      (F.pieceVertex_ne_first j x) (F.pieceVertex_ne_last j x)).choose_spec
  refine ⟨y, (F.piece_iff y j).mpr ?_⟩
  rw [hy]
  change F.start j ≤ F.start j + x.val ∧
    F.start j + x.val < F.start j + F.length j
  have := x.isLt
  omega

@[simp] theorem vertex_pieceMap (j : Fin 3) (x : Fin (F.length j)) :
    F.vertex (F.pieceMap j x).val = F.pieceVertex j x :=
  (F.vertex_surjective (F.pieceVertex j x)
    (F.pieceVertex_ne_first j x) (F.pieceVertex_ne_last j x)).choose_spec

theorem pieceMap_bijective (j : Fin 3) : Function.Bijective (F.pieceMap j) := by
  constructor
  · intro x y h
    have hv := congrArg (fun z : {v : Fin r // F.piece v = j} => (F.vertex z.val).val) h
    simp only [vertex_pieceMap, pieceVertex] at hv
    exact Fin.ext (by omega)
  · intro y
    have hy := (F.piece_iff y.val j).mp y.property
    let x : Fin (F.length j) := ⟨(F.vertex y.val).val - F.start j, by omega⟩
    refine ⟨x, Subtype.ext (F.vertex_injective ?_)⟩
    rw [vertex_pieceMap]
    apply Fin.ext
    change F.start j + ((F.vertex y.val).val - F.start j) = (F.vertex y.val).val
    omega

/-- Actual affine coordinates on each component, not only a count comparison. -/
noncomputable def componentEquiv (j : Fin 3) :
    Fin (F.length j) ≃ {v : Fin r // F.piece v = j} :=
  Equiv.ofBijective (F.pieceMap j) (F.pieceMap_bijective j)

@[simp] theorem vertex_componentEquiv (j : Fin 3) (x : Fin (F.length j)) :
    F.vertex (F.componentEquiv j x).val = F.pieceVertex j x :=
  F.vertex_pieceMap j x

theorem component_rel_even (j : Fin 3) (hp : F.start j % 2 = 0)
    (a b : Fin (F.length j)) :
    F.relation (F.componentEquiv j a).val (F.componentEquiv j b).val ↔
      zigLt (F.length j) a b := by
  change zigLt (r + 2) (F.vertex _) (F.vertex _) ↔ _
  rw [vertex_componentEquiv, vertex_componentEquiv]
  simp only [zigLt, pieceVertex]
  omega

theorem component_rel_odd (j : Fin 3) (hp : F.start j % 2 ≠ 0)
    (a b : Fin (F.length j)) :
    F.relation (F.componentEquiv j a).val (F.componentEquiv j b).val ↔
      zigLt (F.length j) b a := by
  change zigLt (r + 2) (F.vertex _) (F.vertex _) ↔ _
  rw [vertex_componentEquiv, vertex_componentEquiv]
  simp only [zigLt, pieceVertex]
  omega

/-- Every interval component has exactly the fence extension count, whether
its bottom vertex is a minimum or a maximum. -/
theorem component_card (j : Fin 3) :
    Nat.card (ComponentLE F.relation F.piece j) =
      Fintype.card (ZigzagLE (F.length j)) := by
  by_cases hp : F.start j % 2 = 0
  · let e := extensionRelEquiv (fun a b : {v : Fin r // F.piece v = j} =>
      F.relation a.val b.val) (zigLt (F.length j)) (F.componentEquiv j)
      (F.component_rel_even j hp)
    exact (Nat.card_congr e).trans (Nat.card_eq_fintype_card)
  · let e := extensionRelEquiv (fun a b : {v : Fin r // F.piece v = j} =>
      F.relation a.val b.val) (fun a b => zigLt (F.length j) b a) (F.componentEquiv j)
      (F.component_rel_odd j hp)
    exact (Nat.card_congr (e.trans (dualExtensionEquiv (zigLt (F.length j))))).trans
      (Nat.card_eq_fintype_card)

#print axioms componentEquiv
#print axioms component_card
end ResidualFrame
end Zigzag
```

### `FenceFiberClassification.lean`

```lean
import FenceInternalProjection
import FenceResidualConnectivity
import Mathlib.Tactic.FinCases

namespace Zigzag

theorem EndpointFrame.extension_range_iff {r : ℕ} (F : EndpointFrame r)
    (w : ZigzagLE (r + 2)) :
    (∃ v, F.extension v = w) ↔
      w.val 0 = F.vertices.symm none ∧
      w.val (Fin.last (r + 1)) = F.vertices.symm (some none) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨F.pad_first v.val, F.pad_last v.val⟩
  · intro hw
    exact F.exists_pad ⟨w, hw⟩

theorem endpointA_range_iff {r : ℕ} (w : ZigzagLE (r + 2)) :
    (∃ v, endpointA v = w) ↔ w.val 0 = 0 ∧ w.val (Fin.last (r + 1)) = 1 := by
  simpa [frameA, EndpointFrame.extension, EndpointFrame.pad, splitAVertices,
    ← Equiv.optionCongr_symm, endpointA, padA] using
    (frameA r).extension_range_iff w

theorem endpointB_range_iff {r : ℕ} (hr : Even r) (w : ZigzagLE (r + 2)) :
    (∃ v, endpointB hr v = w) ↔
      w.val 0 = 0 ∧ w.val (Fin.last (r + 1)) = Fin.last (r + 1) := by
  simpa only [endpointB, frameB, splitB_first, splitB_last] using
    (frameB r hr).extension_range_iff w

theorem endpointC_range_iff {r : ℕ} (hr : Even r) (w : ZigzagLE (r + 2)) :
    (∃ v, endpointC hr v = w) ↔
      w.val 0 = ⟨r, by omega⟩ ∧ w.val (Fin.last (r + 1)) = Fin.last (r + 1) := by
  simpa only [endpointC, frameC, splitC_first, splitC_last] using
    (frameC r hr).extension_range_iff w

/-- U is exactly the union of the three endpoint pairs in the source proof. -/
theorem inConnectedFibers_iff_endpoints {r : ℕ} (hr : Even r)
    (w : ZigzagLE (r + 2)) :
    InConnectedFibers hr w ↔
      (w.val 0 = 0 ∧ w.val (Fin.last (r + 1)) = 1) ∨
      (w.val 0 = 0 ∧ w.val (Fin.last (r + 1)) = Fin.last (r + 1)) ∨
      (w.val 0 = ⟨r, by omega⟩ ∧ w.val (Fin.last (r + 1)) = Fin.last (r + 1)) := by
  constructor
  · rintro ⟨j, v, rfl⟩
    fin_cases j
    · exact Or.inl ((endpointA_range_iff _).mp ⟨v, rfl⟩)
    · exact Or.inr (Or.inl ((endpointB_range_iff hr _).mp ⟨v, rfl⟩))
    · exact Or.inr (Or.inr ((endpointC_range_iff hr _).mp ⟨v, rfl⟩))
  · intro hw
    rcases hw with hw | hw | hw
    · obtain ⟨v, hv⟩ := (endpointA_range_iff w).mpr hw
      exact ⟨0, v, hv.symm⟩
    · obtain ⟨v, hv⟩ := (endpointB_range_iff hr w).mpr hw
      exact ⟨1, v, hv.symm⟩
    · obtain ⟨v, hv⟩ := (endpointC_range_iff hr w).mpr hw
      exact ⟨2, v, hv.symm⟩

/-- The complement used by badAction consists precisely of extensions with
disconnected literal residual comparability graph. -/
theorem inConnectedFibers_iff_residualConnected {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (w : ZigzagLE (r + 2)) :
    InConnectedFibers hr w ↔ ResidualConnected (w.val 0) (w.val (Fin.last (r + 1))) := by
  have hn : Even (r + 2) := hr.add (by decide : Even 2)
  have hfirst := first_vertex_even (by omega : 0 < r + 2) w
  have hzero : (⟨0, by omega⟩ : Fin (r + 2)) = 0 := by ext; simp
  rw [hzero] at hfirst
  have hlast := last_vertex_odd hn (by omega : 0 < r + 2) w
  have hpos : (⟨r + 2 - 1, by omega⟩ : Fin (r + 2)) = Fin.last (r + 1) := by
    ext; simp
  rw [hpos] at hlast
  rw [inConnectedFibers_iff_endpoints, residual_connected_endpoints (by omega) hn _ _ hfirst hlast]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_last]
  omega

#print axioms endpointA_range_iff
#print axioms endpointB_range_iff
#print axioms endpointC_range_iff
#print axioms inConnectedFibers_iff_residualConnected
end Zigzag
```

### `FenceBadSectionFree.lean`

```lean
import BadFiberReduction
import FenceSectionArithmetic
import ResidualComponentCoordinates
import FenceFiberClassification

namespace Zigzag
open Equiv

/-- Each disconnected residual relation satisfies the uniform section bound:
its interval components are strictly smaller fences or dual fences. -/
theorem ResidualFrame.sectionFree_of_disconnected {r : ℕ} (F : ResidualFrame r)
    (hr : Even r) (h4 : 4 ≤ r) (hd : ¬ ResidualConnected F.first F.last) :
    SectionFree (alternatingGroup (ZigzagLE r)) (relationBK F.relation) := by
  apply residual_sectionFree_of_component_lt hr h4 F.relation F.piece F.relation_piece
  intro j
  rw [F.component_card]
  exact card_smaller_lt hr h4 (F.length_lt_of_disconnected hd j)

/-- The remaining section hypothesis in diagonal isolation is now discharged
uniformly, without an induction hypothesis and without any parity step. -/
theorem badImageSectionFree {r : ℕ} (hr : Even r) (h4 : 4 ≤ r) :
    BadImageSectionFree r hr := by
  apply badImageSectionFree_of_residuals hr h4
  intro w
  apply ResidualFrame.sectionFree_of_disconnected _ hr h4
  have hd := (inConnectedFibers_iff_residualConnected hr h4 w.val).not.mp w.property
  simpa only [ResidualFrame.first, ResidualFrame.last,
    ResidualFrame.ofWord_first, ResidualFrame.ofWord_last] using hd

/-- Literal isolated diagonal alternating action, with no bad-image section
hypothesis left. Only the intended smaller-fence induction hypothesis remains. -/
theorem diagonal_isolation {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) (a : alternatingGroup (ZigzagLE r)) :
    ∃ h ∈ BKgroup (r + 2),
      (∀ w, h (endpointA w) = endpointA (a.val w)) ∧
      (∀ w, h (endpointB hr w) = endpointB hr (a.val w)) ∧
      (∀ w, h (endpointC hr w) = endpointC hr (a.val w)) ∧
      (∀ w, ¬ InConnectedFibers hr w → h w = w) :=
  diagonal_isolation_of_bad_sectionFree hr h4 ih (badImageSectionFree hr h4) a

#print axioms ResidualFrame.sectionFree_of_disconnected
#print axioms badImageSectionFree
#print axioms diagonal_isolation
end Zigzag
```

### `FenceBoundarySwitch.lean`

```lean
import FenceBadSectionFree

namespace Zigzag
open Equiv

/-- Same-parity fence vertices are incomparable. -/
theorem same_parity_incomparable {n : ℕ} (a b : Fin n)
    (hp : a.val % 2 = b.val % 2) : ¬ zigLt n a b ∧ ¬ zigLt n b a := by
  constructor <;> intro h <;> obtain ⟨ha, hab⟩ := h <;> omega

/-- A move fixes every position outside its adjacent pair, whether or not it
swaps. This is equality of the actual word values. -/
theorem move_at_other {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R) (p : Fin n)
    (hl : p ≠ leftPos i hi) (hr : p ≠ rightPos i hi) :
    (move R i hi w).val p = w.val p := by
  rw [move_apply]
  split_ifs
  · simp only [rawSwap, Equiv.trans_apply, adjacentSwap, Equiv.swap_apply_of_ne_of_ne hl hr]
  · rfl

theorem move_at_left {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R)
    (hs : incomparable R i hi w.val) :
    (move R i hi w).val (leftPos i hi) = w.val (rightPos i hi) := by
  rw [move_apply, ite_eq_left hs]
  simp only [rawSwap, Equiv.trans_apply, adjacentSwap, Equiv.swap_apply_left]

theorem move_at_right {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R)
    (hs : incomparable R i hi w.val) :
    (move R i hi w).val (rightPos i hi) = w.val (leftPos i hi) := by
  rw [move_apply, ite_eq_left hs]
  simp only [rawSwap, Equiv.trans_apply, adjacentSwap, Equiv.swap_apply_right]

/-- Source h=t₁t_(n-1), on the literal extension set of n=r+2 vertices. -/
def boundarySwitch (r : ℕ) : Perm (ZigzagLE (r + 2)) :=
  bk (r + 2) 0 (by omega) * bk (r + 2) r (by omega)

theorem boundarySwitch_mem (r : ℕ) : boundarySwitch r ∈ BKgroup (r + 2) :=
  (BKgroup _).mul_mem (bk_mem _ _ _) (bk_mem _ _ _)

/-- Complete pointwise evaluation of the boundary switch under the two
literal incomparability conditions. The two swaps are disjoint for r≥2. -/
theorem boundarySwitch_apply {r : ℕ} (h2 : 2 ≤ r) (w : ZigzagLE (r + 2))
    (hl : incomparable (zigLt (r + 2)) 0 (by omega) w.val)
    (hr : incomparable (zigLt (r + 2)) r (by omega) w.val) (p : Fin (r + 2)) :
    (boundarySwitch r w).val p =
      w.val (adjacentSwap r (by omega) (adjacentSwap 0 (by omega) p)) := by
  have hfirst (p : Fin (r + 2)) (hp : p.val < r) :
      (bk (r + 2) r (by omega) w).val p = w.val p := by
    apply move_at_other
    · intro he; have := congrArg Fin.val he; change p.val = r at this; omega
    · intro he; have := congrArg Fin.val he; change p.val = r + 1 at this; omega
  have hl' : incomparable (zigLt (r + 2)) 0 (by omega)
      (bk (r + 2) r (by omega) w).val := by
    unfold incomparable at hl ⊢
    rw [hfirst _ (by change 0 < r; omega), hfirst _ (by change 1 < r; omega)]
    exact hl
  change (bk (r + 2) 0 _ (bk (r + 2) r _ w)).val p = _
  rw [show (bk (r + 2) 0 _ (bk (r + 2) r _ w)).val = _ from
    move_apply (zigLt (r + 2)) 0 (by omega) _, ite_eq_left hl']
  change (bk (r + 2) r _ w).val (adjacentSwap 0 _ p) = _
  rw [show (bk (r + 2) r _ w).val = _ from
    move_apply (zigLt (r + 2)) r (by omega) w, ite_eq_left hr]
  rfl

/-- The four changed positions, used by the source's endpoint-fiber test. -/
theorem boundarySwitch_ends {r : ℕ} (h2 : 2 ≤ r) (w : ZigzagLE (r + 2))
    (hl : incomparable (zigLt (r + 2)) 0 (by omega) w.val)
    (hr : incomparable (zigLt (r + 2)) r (by omega) w.val) :
    (boundarySwitch r w).val 0 = w.val 1 ∧
    (boundarySwitch r w).val 1 = w.val 0 ∧
    (boundarySwitch r w).val ⟨r, by omega⟩ = w.val (Fin.last (r + 1)) ∧
    (boundarySwitch r w).val (Fin.last (r + 1)) = w.val ⟨r, by omega⟩ := by
  have hne (a b : Fin (r + 2)) (h : a.val ≠ b.val) : a ≠ b :=
    fun he => h (congrArg Fin.val he)
  have hf : adjacentSwap 0 (by omega : 0 + 1 < r + 2) 0 = 1 :=
    Equiv.swap_apply_left _ _
  have hf' : adjacentSwap 0 (by omega : 0 + 1 < r + 2) 1 = 0 :=
    Equiv.swap_apply_right _ _
  have he : adjacentSwap r (by omega : r + 1 < r + 2) ⟨r, by omega⟩ =
      Fin.last (r + 1) := Equiv.swap_apply_left _ _
  have he' : adjacentSwap r (by omega : r + 1 < r + 2) (Fin.last (r + 1)) =
      ⟨r, by omega⟩ := Equiv.swap_apply_right _ _
  have ho (p : Fin (r + 2)) (hp : 2 ≤ p.val) : adjacentSwap 0 (by omega : 0 + 1 < r + 2) p = p := by
    unfold adjacentSwap
    apply Equiv.swap_apply_of_ne_of_ne
    · exact hne _ _ (by change p.val ≠ 0; omega)
    · exact hne _ _ (by change p.val ≠ 1; omega)
  have hi (p : Fin (r + 2)) (hp : p.val < r) : adjacentSwap r (by omega : r + 1 < r + 2) p = p := by
    unfold adjacentSwap
    apply Equiv.swap_apply_of_ne_of_ne
    · exact hne _ _ (by change p.val ≠ r; omega)
    · exact hne _ _ (by change p.val ≠ r + 1; omega)
  simp only [boundarySwitch_apply h2 w hl hr, hf, hf',
    ho ⟨r, by omega⟩ (by change 2 ≤ r; omega),
    ho (Fin.last (r + 1)) (by change 2 ≤ r + 1; omega),
    hi 0 (by change 0 < r; omega), hi 1 (by change 1 < r; omega), he, he', and_self]

#print axioms boundarySwitch_apply
#print axioms boundarySwitch_ends
end Zigzag
```

### `FenceBoundaryFibers.lean`

```lean
import FenceBoundarySwitch

namespace Zigzag
open Equiv

/-- A numerical form of the source endpoint test. -/
theorem connected_values {r : ℕ} (hr : Even r) (w : ZigzagLE (r + 2)) :
    InConnectedFibers hr w ↔
      ((w.val 0).val = 0 ∧ (w.val (Fin.last (r + 1))).val = 1) ∨
      ((w.val 0).val = 0 ∧ (w.val (Fin.last (r + 1))).val = r + 1) ∨
      ((w.val 0).val = r ∧ (w.val (Fin.last (r + 1))).val = r + 1) := by
  simp only [inConnectedFibers_iff_endpoints, Fin.ext_iff, Fin.val_zero,
    Fin.val_one, Fin.val_last]

/-- Boundary swaps are legal when the two letters at each end have equal parity. -/
theorem boundarySwitch_values {r : ℕ} (h2 : 2 ≤ r) (w : ZigzagLE (r + 2))
    (hl : (w.val 0).val % 2 = (w.val 1).val % 2)
    (hh : (w.val ⟨r, by omega⟩).val % 2 =
      (w.val (Fin.last (r + 1))).val % 2) :
    (boundarySwitch r w).val 0 = w.val 1 ∧
    (boundarySwitch r w).val (Fin.last (r + 1)) = w.val ⟨r, by omega⟩ := by
  have he := boundarySwitch_ends h2 w
    (same_parity_incomparable _ _ hl) (same_parity_incomparable _ _ hh)
  exact ⟨he.1, he.2.2.2⟩

private theorem middle_positions {r : ℕ} (h2 : 2 ≤ r) :
    (⟨0, by omega⟩ : Fin r).castSucc.succ = (1 : Fin (r + 2)) ∧
    (⟨r - 1, by omega⟩ : Fin r).castSucc.succ = ⟨r, by omega⟩ := by
  constructor
  · rfl
  · apply Fin.ext
    dsimp
    omega

/-- The h-images of the A fiber have endpoint values w₁+2,wᵣ+2. -/
theorem boundarySwitch_A_ends {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    ((boundarySwitch r (endpointA w)).val 0).val = (w.val ⟨0, by omega⟩).val + 2 ∧
    ((boundarySwitch r (endpointA w)).val (Fin.last (r + 1))).val =
      (w.val ⟨r - 1, by omega⟩).val + 2 := by
  have hp := middle_positions h2
  have hf := first_vertex_even (by omega : 0 < r) w
  have he := last_vertex_odd hr (by omega : 0 < r) w
  have hm0 := padA_middle w.val (⟨0, by omega⟩ : Fin r)
  have hml := padA_middle w.val (⟨r - 1, by omega⟩ : Fin r)
  rw [hp.1] at hm0
  rw [hp.2] at hml
  have hv := boundarySwitch_values h2 (endpointA w)
    (by change (padA w.val 0).val % 2 = (padA w.val 1).val % 2
        rw [padA_first, hm0]; simp only [Fin.val_zero, Fin.val_succ]; omega)
    (by change (padA w.val ⟨r, by omega⟩).val % 2 =
          (padA w.val (Fin.last (r + 1))).val % 2
        rw [padA_last, hml]; simp only [Fin.val_one, Fin.val_succ]; omega)
  constructor
  · exact congrArg Fin.val (hv.1.trans hm0)
  · exact congrArg Fin.val (hv.2.trans hml)

/-- The B-image never returns to the three connected fibers. -/
theorem boundarySwitch_B_ends {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    ((boundarySwitch r (endpointB hr w)).val 0).val = r - (w.val ⟨0, by omega⟩).val ∧
    ((boundarySwitch r (endpointB hr w)).val (Fin.last (r + 1))).val =
      r - (w.val ⟨r - 1, by omega⟩).val := by
  have hp := middle_positions h2
  have hf := first_vertex_even (by omega : 0 < r) w
  have he := last_vertex_odd hr (by omega : 0 < r) w
  have hr0 : r % 2 = 0 := by obtain ⟨k, hk⟩ := hr; omega
  have hfB := endpointB_middle hr w (⟨0, by omega⟩ : Fin r)
  have hlB := endpointB_middle hr w (⟨r - 1, by omega⟩ : Fin r)
  rw [hp.1] at hfB
  rw [hp.2] at hlB
  have hfv := (w.val ⟨0, by omega⟩).isLt
  have hlv := (w.val ⟨r - 1, by omega⟩).isLt
  have hv := boundarySwitch_values h2 (endpointB hr w)
    (by rw [endpointB_first, hfB]; change 0 % 2 = (r - _) % 2; omega)
    (by rw [endpointB_last, hlB]; change (r - _) % 2 = (r + 1) % 2; omega)
  exact ⟨congrArg Fin.val (hv.1.trans hfB), congrArg Fin.val (hv.2.trans hlB)⟩

/-- The h-images of the C fiber have the unchanged smaller endpoint values. -/
theorem boundarySwitch_C_ends {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    ((boundarySwitch r (endpointC hr w)).val 0).val = (w.val ⟨0, by omega⟩).val ∧
    ((boundarySwitch r (endpointC hr w)).val (Fin.last (r + 1))).val =
      (w.val ⟨r - 1, by omega⟩).val := by
  have hp := middle_positions h2
  have hf := first_vertex_even (by omega : 0 < r) w
  have he := last_vertex_odd hr (by omega : 0 < r) w
  have hr0 : r % 2 = 0 := by obtain ⟨k, hk⟩ := hr; omega
  have hfC := endpointC_middle hr w (⟨0, by omega⟩ : Fin r)
  have hlC := endpointC_middle hr w (⟨r - 1, by omega⟩ : Fin r)
  rw [hp.1] at hfC
  rw [hp.2] at hlC
  have hv := boundarySwitch_values h2 (endpointC hr w)
    (by rw [endpointC_first, hfC]; change r % 2 = _; dsimp only; omega)
    (by rw [endpointC_last, hlC]; change _ = (r + 1) % 2; dsimp only; omega)
  exact ⟨congrArg Fin.val (hv.1.trans hfC), congrArg Fin.val (hv.2.trans hlC)⟩

/-- Source R and L in the unchanged literal extension coordinates. -/
def RightWitness {r : ℕ} (h2 : 2 ≤ r) (w : ZigzagLE r) : Prop :=
  (w.val ⟨0, by omega⟩).val = r - 2 ∧ (w.val ⟨r - 1, by omega⟩).val = r - 1

def LeftWitness {r : ℕ} (h2 : 2 ≤ r) (w : ZigzagLE r) : Prop :=
  (w.val ⟨0, by omega⟩).val = 0 ∧ (w.val ⟨r - 1, by omega⟩).val = 1

theorem boundarySwitch_A_connected {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    InConnectedFibers hr (boundarySwitch r (endpointA w)) ↔ RightWitness h2 w := by
  rw [connected_values]
  have he := boundarySwitch_A_ends hr h2 w
  dsimp [RightWitness]
  omega

theorem boundarySwitch_B_not_connected {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) : ¬ InConnectedFibers hr (boundarySwitch r (endpointB hr w)) := by
  rw [connected_values]
  have he := boundarySwitch_B_ends hr h2 w
  have hf := (w.val ⟨0, by omega⟩).isLt
  have hl := (w.val ⟨r - 1, by omega⟩).isLt
  omega

theorem boundarySwitch_C_connected {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    InConnectedFibers hr (boundarySwitch r (endpointC hr w)) ↔ LeftWitness h2 w := by
  rw [connected_values]
  have he := boundarySwitch_C_ends hr h2 w
  have hf := (w.val ⟨0, by omega⟩).isLt
  have hl := (w.val ⟨r - 1, by omega⟩).isLt
  dsimp [LeftWitness]
  omega

#print axioms boundarySwitch_A_connected
#print axioms boundarySwitch_B_not_connected
#print axioms boundarySwitch_C_connected
end Zigzag
```

### `FenceSupportWitnesses.lean`

```lean
import FenceBoundaryFibers
import ZigzagBases
import FiniteLinearExtension

namespace Zigzag
open Equiv

/-- Two different neutral words. B-fiber words suffice except at size four,
where two of the five already enumerated extensions are used. -/
theorem two_neutral_witnesses (r : ℕ) (hr : Even r) (h4 : 4 ≤ r) :
    ∃ z z' : ZigzagLE r, z ≠ z' ∧
      ¬ RightWitness (by omega : 2 ≤ r) z ∧ ¬ LeftWitness (by omega : 2 ≤ r) z ∧
      ¬ RightWitness (by omega : 2 ≤ r) z' ∧ ¬ LeftWitness (by omega : 2 ≤ r) z' := by
  by_cases he : r = 4
  · subst r
    refine ⟨leFour 0, leFour 3, by decide, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [RightWitness, LeftWitness, leFour, wordFour]
  · obtain ⟨q, rfl⟩ : ∃ q, r = q+2 := ⟨r-2, by omega⟩
    have hp : Even q := by obtain ⟨k, hk⟩ := hr; exact ⟨k-1, by omega⟩
    have hq : 4 ≤ q := by obtain ⟨k, hk⟩ := hp; omega
    have hc := five_le_card q hp hq
    have ht : Nontrivial (ZigzagLE q) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨u, v, huv⟩ := exists_pair_ne (ZigzagLE q)
    have hb := (frameB q hp).extension_injective.ne huv
    have hx (w : ZigzagLE q) :
        ¬ RightWitness (by omega : 2 ≤ q+2) (endpointB hp w) ∧
        ¬ LeftWitness (by omega : 2 ≤ q+2) (endpointB hp w) := by
      have hf := endpointB_first hp w
      have hl := endpointB_last hp w
      dsimp [RightWitness, LeftWitness]
      change ¬ (( (endpointB hp w).val 0).val = q ∧
        ((endpointB hp w).val (Fin.last (q+1))).val = q+1) ∧
        ¬ (((endpointB hp w).val 0).val = 0 ∧
        ((endpointB hp w).val (Fin.last (q+1))).val = 1)
      rw [hf, hl]
      simp only [Fin.val_zero, Fin.val_last]
      constructor <;> omega
    exact ⟨endpointB hp u, endpointB hp v, hb, (hx u).1, (hx u).2, (hx v).1, (hx v).2⟩

/-- A word in R is obtained from the existing literal C embedding. -/
theorem right_witness_exists (r : ℕ) (hr : Even r) (h4 : 4 ≤ r) :
    ∃ s : ZigzagLE r, RightWitness (by omega : 2 ≤ r) s := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q+2 := ⟨r-2, by omega⟩
  have hp : Even q := by obtain ⟨k, hk⟩ := hr; exact ⟨k-1, by omega⟩
  have hu : Nonempty (ZigzagLE q) := by
    have hh := finite_linear_extension (Fin q) (zigLt q)
    rw [Fintype.card_fin] at hh
    exact hh
  obtain ⟨u⟩ := hu
  refine ⟨endpointC hp u, ?_⟩
  change ((endpointC hp u).val 0).val = q ∧
    ((endpointC hp u).val (Fin.last (q+1))).val = q+1
  rw [endpointC_first, endpointC_last]
  exact ⟨rfl, rfl⟩

/-- The two exceptional boundary sets are disjoint. -/
theorem right_not_left {r : ℕ} (h4 : 4 ≤ r) {w : ZigzagLE r}
    (hw : RightWitness (by omega : 2 ≤ r) w) :
    ¬ LeftWitness (by omega : 2 ≤ r) w := by
  dsimp [RightWitness, LeftWitness] at *
  omega

#print axioms two_neutral_witnesses
#print axioms right_witness_exists
end Zigzag
```

### `FenceBoundaryCorrespondence.lean`

```lean
import FenceSupportWitnesses

namespace Zigzag
open Equiv
set_option linter.unusedSimpArgs false

/-- Applying the boundary switch twice returns the original word, whenever
both boundary swaps are legal. No assertion about other words is used. -/
theorem boundarySwitch_twice_of_legal {r : ℕ} (h2 : 2 ≤ r)
    (w : ZigzagLE (r + 2))
    (hl : incomparable (zigLt (r + 2)) 0 (by omega) w.val)
    (hh : incomparable (zigLt (r + 2)) r (by omega) w.val) :
    boundarySwitch r (boundarySwitch r w) = w := by
  have he := boundarySwitch_ends h2 w hl hh
  have hl' : incomparable (zigLt (r + 2)) 0 (by omega)
      (boundarySwitch r w).val := by
    change ¬ zigLt _ ((boundarySwitch r w).val 0) ((boundarySwitch r w).val 1) ∧
      ¬ zigLt _ ((boundarySwitch r w).val 1) ((boundarySwitch r w).val 0)
    rw [he.1, he.2.1]
    exact ⟨hl.2, hl.1⟩
  have hh' : incomparable (zigLt (r + 2)) r (by omega)
      (boundarySwitch r w).val := by
    change ¬ zigLt _ ((boundarySwitch r w).val ⟨r, by omega⟩)
        ((boundarySwitch r w).val (Fin.last (r + 1))) ∧
      ¬ zigLt _ ((boundarySwitch r w).val (Fin.last (r + 1)))
        ((boundarySwitch r w).val ⟨r, by omega⟩)
    rw [he.2.2.1, he.2.2.2]
    exact ⟨hh.2, hh.1⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [boundarySwitch_apply h2 _ hl' hh', boundarySwitch_apply h2 _ hl hh]
  have commute (p : Fin (r + 2)) :
      adjacentSwap 0 (by omega : 0 + 1 < r + 2) (adjacentSwap r (by omega) p) =
      adjacentSwap r (by omega) (adjacentSwap 0 (by omega) p) := by
    have h0 : r ≠ 0 := by omega
    have h1 : r ≠ 1 := by omega
    have h10 : r+1 ≠ 0 := by omega
    have h11 : r+1 ≠ 1 := by omega
    by_cases hp0 : p.val = 0
    · simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos,
        Fin.ext_iff, hp0, h0, h1, h10, h11, Ne.symm h0, Ne.symm h1]
    by_cases hp1 : p.val = 1
    · simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos,
        Fin.ext_iff, hp1, h0, h1, h10, h11, Ne.symm h0, Ne.symm h1]
    by_cases hpr : p.val = r
    · simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos,
        Fin.ext_iff, hpr, h0, h1, h10, h11, Ne.symm h0, Ne.symm h1]
    by_cases hpr' : p.val = r+1
    · simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos,
        Fin.ext_iff, hpr', h0, h1, h10, h11, Ne.symm h0, Ne.symm h1]
    · simp [adjacentSwap, Equiv.swap_apply_def, leftPos, rightPos,
        Fin.ext_iff, hp0, hp1, hpr, hpr']
  rw [commute]
  simp only [adjacentSwap, Equiv.swap_apply_self]

/-- Legality of both boundary swaps on A, recorded for the inverse identity. -/
theorem boundarySwitch_A_legal {r : ℕ} (hr : Even r) (h2 : 2 ≤ r)
    (w : ZigzagLE r) :
    incomparable (zigLt (r + 2)) 0 (by omega) (endpointA w).val ∧
    incomparable (zigLt (r + 2)) r (by omega) (endpointA w).val := by
  have hp0 : (⟨0, by omega⟩ : Fin r).castSucc.succ = (1 : Fin (r+2)) := Fin.ext rfl
  have hpl : (⟨r-1, by omega⟩ : Fin r).castSucc.succ = ⟨r, by omega⟩ := by
    apply Fin.ext; dsimp; omega
  have hm0 := padA_middle w.val (⟨0, by omega⟩ : Fin r)
  have hml := padA_middle w.val (⟨r-1, by omega⟩ : Fin r)
  rw [hp0] at hm0
  rw [hpl] at hml
  have hf := first_vertex_even (by omega : 0 < r) w
  have hl := last_vertex_odd hr (by omega : 0 < r) w
  constructor
  · apply same_parity_incomparable
    change (padA w.val 0).val % 2 = (padA w.val 1).val % 2
    rw [padA_first, hm0]
    simp only [Fin.val_zero, Fin.val_succ]
    omega
  · apply same_parity_incomparable
    change (padA w.val ⟨r, by omega⟩).val % 2 =
      (padA w.val (Fin.last (r+1))).val % 2
    rw [padA_last, hml]
    simp only [Fin.val_one, Fin.val_succ]
    omega

/-- Exact source correspondence h A(s)=C(t), with t in L. The literal C-fiber
surjectivity supplies t; its two endpoint values follow from the inner swaps. -/
theorem right_left_correspondence {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (s : ZigzagLE r) (hs : RightWitness (by omega : 2 ≤ r) s) :
    ∃ t : ZigzagLE r, LeftWitness (by omega : 2 ≤ r) t ∧
      boundarySwitch r (endpointA s) = endpointC hr t ∧
      boundarySwitch r (endpointC hr t) = endpointA s := by
  have h2 : 2 ≤ r := by omega
  have he := boundarySwitch_A_ends hr h2 s
  have hc : ∃ t, endpointC hr t = boundarySwitch r (endpointA s) := by
    apply (endpointC_range_iff hr _).mpr
    constructor <;> apply Fin.ext
    · change _ = r
      dsimp [RightWitness] at hs
      omega
    · change _ = r+1
      dsimp [RightWitness] at hs
      omega
  obtain ⟨t, ht⟩ := hc
  have hlegal := boundarySwitch_A_legal hr h2 s
  have hi := boundarySwitch_ends h2 (endpointA s) hlegal.1 hlegal.2
  have hp0 : (⟨0, by omega⟩ : Fin r).castSucc.succ = (1 : Fin (r+2)) := Fin.ext rfl
  have hpl : (⟨r-1, by omega⟩ : Fin r).castSucc.succ = ⟨r, by omega⟩ := by
    apply Fin.ext; dsimp; omega
  have hm0 := endpointC_middle hr t (⟨0, by omega⟩ : Fin r)
  have hml := endpointC_middle hr t (⟨r-1, by omega⟩ : Fin r)
  rw [hp0, ht] at hm0
  rw [hpl, ht] at hml
  have hf : (endpointA s).val 0 = 0 := padA_first s.val
  have hl : (endpointA s).val (Fin.last (r+1)) = 1 := padA_last s.val
  rw [hi.2.1, hf] at hm0
  rw [hi.2.2.1, hl] at hml
  refine ⟨t, ⟨?_, ?_⟩, ht.symm, ?_⟩
  · exact (congrArg Fin.val hm0).symm
  · exact (congrArg Fin.val hml).symm
  · rw [ht]
    exact boundarySwitch_twice_of_legal h2 _ hlegal.1 hlegal.2

#print axioms right_left_correspondence
end Zigzag
```

### `DiagonalSupport.lean`

```lean
import FenceBoundaryCorrespondence
import SingletonCommutator

namespace Zigzag
open Equiv Equiv.Perm

/-- The exact action supplied by isolation, kept as a specification rather than
a new definition of the Bender–Knuth group. -/
def IsDiagonal {r : ℕ} (hr : Even r) (f : Perm (ZigzagLE r))
    (g : Perm (ZigzagLE (r+2))) : Prop :=
  (∀ w, g (endpointA w) = endpointA (f w)) ∧
  (∀ w, g (endpointB hr w) = endpointB hr (f w)) ∧
  (∀ w, g (endpointC hr w) = endpointC hr (f w)) ∧
  (∀ w, ¬ InConnectedFibers hr w → g w = w)

theorem diagonal_exists {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) (f : alternatingGroup (ZigzagLE r)) :
    ∃ g ∈ BKgroup (r+2), IsDiagonal hr f.val g :=
  diagonal_isolation hr h4 ih f

theorem diagonal_moved_connected {r : ℕ} {hr : Even r}
    {f : Perm (ZigzagLE r)} {g : Perm (ZigzagLE (r+2))}
    (hg : IsDiagonal hr f g) {x : ZigzagLE (r+2)} (hx : g x ≠ x) :
    InConnectedFibers hr x := by
  by_contra hc
  exact hx (hg.2.2.2 x hc)

/-- Every moved point of a diagonal comes from a moved smaller coordinate. -/
theorem diagonal_moved_coordinates {r : ℕ} {hr : Even r}
    {f : Perm (ZigzagLE r)} {g : Perm (ZigzagLE (r+2))}
    (hg : IsDiagonal hr f g) {x : ZigzagLE (r+2)} (hx : g x ≠ x) :
    ∃ w, f w ≠ w ∧ (x = endpointA w ∨ x = endpointB hr w ∨ x = endpointC hr w) := by
  have hc := diagonal_moved_connected hg hx
  obtain ⟨j,w,hw⟩ := hc
  fin_cases j
  · change x = endpointA w at hw
    refine ⟨w, ?_, Or.inl hw⟩
    intro he
    exact hx (by rw [hw, hg.1, he])
  · change x = endpointB hr w at hw
    refine ⟨w, ?_, Or.inr (Or.inl hw)⟩
    intro he
    exact hx (by rw [hw, hg.2.1, he])
  · change x = endpointC hr w at hw
    refine ⟨w, ?_, Or.inr (Or.inr hw)⟩
    intro he
    exact hx (by rw [hw, hg.2.2.1, he])

/-- Elementary support control for the chosen smaller 3-cycle. -/
theorem cycle_moved_three {α : Type*} [DecidableEq α] (s z z' x : α)
    (hx : (swap z s * swap z z') x ≠ x) : x = s ∨ x = z ∨ x = z' := by
  by_contra h
  have hs : x ≠ s := fun he => h (Or.inl he)
  have hz : x ≠ z := fun he => h (Or.inr (Or.inl he))
  have hz' : x ≠ z' := fun he => h (Or.inr (Or.inr he))
  exact hx (by simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hz hz',
    swap_apply_of_ne_of_ne hz hs])

/-- Singleton intersection of the actual two diagonal lifts. This contains no
primitivity or propagation assumption. -/
theorem diagonal_singleton_intersection {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (s t z z' : ZigzagLE r)
    (ht : LeftWitness (by omega : 2 ≤ r) t)
    (hzR : ¬ RightWitness (by omega : 2 ≤ r) z)
    (hzL : ¬ LeftWitness (by omega : 2 ≤ r) z)
    (hz'R : ¬ RightWitness (by omega : 2 ≤ r) z')
    (hz'L : ¬ LeftWitness (by omega : 2 ≤ r) z')
    (hst : boundarySwitch r (endpointC hr t) = endpointA s)
    (a d : Perm (ZigzagLE (r+2)))
    (ha : IsDiagonal hr (swap z s * swap z z') a)
    (hd : IsDiagonal hr (swap z t * swap z z') d) :
    ∀ x, a x ≠ x →
      (boundarySwitch r * d * (boundarySwitch r)⁻¹) x ≠ x → x = endpointA s := by
  intro x hax hbx
  have hU := diagonal_moved_connected ha hax
  let h := boundarySwitch r
  have hdy : d (h⁻¹ x) ≠ h⁻¹ x := by
    intro he
    apply hbx
    change h (d (h⁻¹ x)) = x
    rw [he]
    exact h.apply_symm_apply x
  obtain ⟨w, hw, hwx⟩ := diagonal_moved_coordinates hd hdy
  have hw3 := cycle_moved_three t z z' w hw
  have htR : ¬ RightWitness (by omega : 2 ≤ r) t := by
    intro hh
    exact right_not_left h4 hh ht
  have solve (w : ZigzagLE r) (hwR : ¬ RightWitness (by omega : 2 ≤ r) w)
      (hwL : ¬ LeftWitness (by omega : 2 ≤ r) w) :
      h⁻¹ x ≠ endpointA w ∧ h⁻¹ x ≠ endpointB hr w ∧ h⁻¹ x ≠ endpointC hr w := by
    have hx (v : ZigzagLE (r+2)) (hv : ¬ InConnectedFibers hr (h v)) : h⁻¹ x ≠ v := by
      intro he
      have he' : x = h v := by rw [← he]; exact (h.apply_symm_apply x).symm
      exact hv (he' ▸ hU)
    exact ⟨hx _ (fun hc => hwR ((boundarySwitch_A_connected hr (by omega) w).mp hc)),
      hx _ (boundarySwitch_B_not_connected hr (by omega) w),
      hx _ (fun hc => hwL ((boundarySwitch_C_connected hr (by omega) w).mp hc))⟩
  rcases hw3 with hwt | hwz | hwz'
  · subst w
    rcases hwx with he | he | he
    · have he' : x = h (endpointA t) := by rw [← he]; exact (h.apply_symm_apply x).symm
      exact False.elim (htR ((boundarySwitch_A_connected hr (by omega) t).mp (he' ▸ hU)))
    · have he' : x = h (endpointB hr t) := by rw [← he]; exact (h.apply_symm_apply x).symm
      exact False.elim (boundarySwitch_B_not_connected hr (by omega) t (he' ▸ hU))
    · have he' : x = h (endpointC hr t) := by rw [← he]; exact (h.apply_symm_apply x).symm
      exact he'.trans hst
  · subst w
    have hh := solve z hzR hzL
    rcases hwx with he | he | he
    · exact False.elim (hh.1 he)
    · exact False.elim (hh.2.1 he)
    · exact False.elim (hh.2.2 he)
  · subst w
    have hh := solve z' hz'R hz'L
    rcases hwx with he | he | he
    · exact False.elim (hh.1 he)
    · exact False.elim (hh.2.1 he)
    · exact False.elim (hh.2.2 he)

#print axioms diagonal_singleton_intersection
end Zigzag
```

### `FenceThreeCycle.lean`

```lean
import DiagonalSupport

namespace Zigzag
open Equiv Equiv.Perm

/-- The isolated cycle has two specified points in the A fiber and its third
point outside all three connected fibers. This stronger interface is useful
for the subsequent primitivity argument. -/
theorem isolated_threeCycle {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) :
    ∃ (s z : ZigzagLE r) (e : ZigzagLE (r+2)), s ≠ z ∧
      ¬ InConnectedFibers hr e ∧
      swap (endpointA z) (endpointA s) * swap (endpointA z) e ∈ BKgroup (r+2) := by
  obtain ⟨s, hs⟩ := right_witness_exists r hr h4
  obtain ⟨t, ht, hst, hts⟩ := right_left_correspondence hr h4 s hs
  obtain ⟨z,z',hzz',hzR,hzL,hz'R,hz'L⟩ := two_neutral_witnesses r hr h4
  have hsz : s ≠ z := fun he => hzR (he ▸ hs)
  have hsz' : s ≠ z' := fun he => hz'R (he ▸ hs)
  have htz : t ≠ z := fun he => hzL (he ▸ ht)
  have htz' : t ≠ z' := fun he => hz'L (he ▸ ht)
  let f : Perm (ZigzagLE r) := swap z s * swap z z'
  let k : Perm (ZigzagLE r) := swap z t * swap z z'
  have hf : f ∈ alternatingGroup (ZigzagLE r) :=
    (isThreeCycle_swap_mul_swap_same hsz.symm hzz' hsz').mem_alternatingGroup
  have hk : k ∈ alternatingGroup (ZigzagLE r) :=
    (isThreeCycle_swap_mul_swap_same htz.symm hzz' htz').mem_alternatingGroup
  obtain ⟨a,ha,haD⟩ := diagonal_exists hr h4 ih ⟨f,hf⟩
  obtain ⟨d,hd,hdD⟩ := diagonal_exists hr h4 ih ⟨k,hk⟩
  let h := boundarySwitch r
  let b := h * d * h⁻¹
  let e := h (endpointC hr z)
  have he : ¬ InConnectedFibers hr e := by
    intro hc
    exact hzL ((boundarySwitch_C_connected hr (by omega) z).mp hc)
  have hfs : f s = z := by
    simp [f, Perm.mul_apply, swap_apply_def, hsz, hsz']
  have hkt : k t = z := by
    simp [k, Perm.mul_apply, swap_apply_def, htz, htz']
  have has : a (endpointA s) = endpointA z := by rw [haD.1, hfs]
  have hpre : h⁻¹ (endpointA s) = endpointC hr t := by
    apply h.injective
    exact (h.apply_symm_apply _).trans hts.symm
  have hbs : b (endpointA s) = e := by
    change h (d (h⁻¹ (endpointA s))) = e
    rw [hpre, hdD.2.2.1, hkt]
  have hasne : a (endpointA s) ≠ endpointA s := by
    rw [has]
    exact (endpointA_injective r).ne hsz.symm
  have hAsU : InConnectedFibers hr (endpointA s) := ⟨0,s,rfl⟩
  have hbsne : b (endpointA s) ≠ endpointA s := by
    rw [hbs]
    exact fun hh => he (hh ▸ hAsU)
  have hint := diagonal_singleton_intersection hr h4 s t z z' ht hzR hzL hz'R hz'L hts
    a d haD hdD
  have hcomm := commutator_singleton a b (endpointA s) hasne hbsne hint
  have hb : b ∈ BKgroup (r+2) :=
    (BKgroup _).mul_mem ((BKgroup _).mul_mem (boundarySwitch_mem r) hd)
      ((BKgroup _).inv_mem (boundarySwitch_mem r))
  have hc : a * b * a⁻¹ * b⁻¹ ∈ BKgroup (r+2) :=
    (BKgroup _).mul_mem ((BKgroup _).mul_mem ((BKgroup _).mul_mem ha hb)
      ((BKgroup _).inv_mem ha)) ((BKgroup _).inv_mem hb)
  rw [hcomm, has, hbs] at hc
  exact ⟨s,z,e,hsz,he,hc⟩

/-- A literal single 3-cycle in every inductive even order. -/
theorem threeCycle_mem {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) :
    ∃ g ∈ BKgroup (r+2), g.IsThreeCycle := by
  obtain ⟨s,z,e,hsz,he,hg⟩ := isolated_threeCycle hr h4 ih
  refine ⟨_,hg, isThreeCycle_swap_mul_swap_same ((endpointA_injective r).ne hsz.symm) ?_ ?_⟩
  · intro hh
    apply he
    rw [← hh]
    exact ⟨0,z,rfl⟩
  · intro hh
    apply he
    rw [← hh]
    exact ⟨0,s,rfl⟩

/-- The n-based interface specified by the design. -/
theorem threeCycle_step (n : ℕ) (hn : Even n) (h6 : 6 ≤ n)
    (ih : BKgroup (n-2) = ⊤) : ∃ g ∈ BKgroup n, g.IsThreeCycle := by
  obtain ⟨r,rfl⟩ : ∃ r, n = r+2 := ⟨n-2,by omega⟩
  have hr : Even r := by obtain ⟨k,hk⟩ := hn; exact ⟨k-1,by omega⟩
  exact threeCycle_mem hr (by omega) ih

#print axioms isolated_threeCycle
#print axioms threeCycle_mem
#print axioms threeCycle_step
end Zigzag
```

### `FenceSupportedCycles.lean`

```lean
import FenceThreeCycle
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic.Group

namespace Zigzag
open Equiv Equiv.Perm
set_option linter.unusedSimpArgs false

private theorem conjugate_pair {α : Type*} [DecidableEq α]
    (h : Perm α) (a b c : α) :
    h * (swap a b * swap a c) * h⁻¹ = swap (h a) (h b) * swap (h a) (h c) := by
  calc
    _ = (h * swap a b * h⁻¹) * (h * swap a c * h⁻¹) := by group
    _ = _ := by simp only [← swap_apply_apply]

/-- Every ordered pair of distinct A-points occurs with the SAME external
point e in an actual supported 3-cycle of BK. -/
theorem all_star_cycles {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) :
    ∃ e : ZigzagLE (r+2), ¬ InConnectedFibers hr e ∧
      ∀ x y : ZigzagLE r, x ≠ y →
        swap (endpointA x) (endpointA y) * swap (endpointA x) e ∈ BKgroup (r+2) := by
  obtain ⟨s,z,e,hsz,he,hc⟩ := isolated_threeCycle hr h4 ih
  have hm := alternatingGroup.isMultiplyPretransitive (ZigzagLE r)
  have hc5 : 5 ≤ Nat.card (ZigzagLE r) := by
    simpa only [Nat.card_eq_fintype_card] using five_le_card r hr h4
  have htwo : MulAction.IsMultiplyPretransitive
      (alternatingGroup (ZigzagLE r)) (ZigzagLE r) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by omega : 2 ≤ Nat.card (ZigzagLE r)-2)
      (by omega : Nat.card (ZigzagLE r)-2 ≤ Nat.card (ZigzagLE r))
  refine ⟨e,he,?_⟩
  intro x y hxy
  obtain ⟨f,hfx,hfy⟩ := (MulAction.is_two_pretransitive_iff.mp htwo) hsz.symm hxy
  obtain ⟨d,hd,hdD⟩ := diagonal_exists hr h4 ih f
  have hdx : d (endpointA z) = endpointA x := by
    rw [hdD.1]
    exact congrArg endpointA hfx
  have hdy : d (endpointA s) = endpointA y := by
    rw [hdD.1]
    exact congrArg endpointA hfy
  have hde : d e = e := hdD.2.2.2 e he
  have hh := (BKgroup _).mul_mem ((BKgroup _).mul_mem hd hc) ((BKgroup _).inv_mem hd)
  rwa [conjugate_pair, hdx, hdy, hde] at hh

/-- Two cycles through an external point multiply to an internal 3-cycle. -/
private theorem star_product {α : Type*} [DecidableEq α]
    (e a b c : α) (hea : e ≠ a) (heb : e ≠ b) (hec : e ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap a e) * (swap c a * swap c e) = swap a b * swap a c := by
  ext x
  by_cases hxe : x = e
  · subst x; simp [Perm.mul_apply, swap_apply_def, *, Ne.symm hea, Ne.symm heb, Ne.symm hec, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  by_cases hxa : x = a
  · subst x; simp [Perm.mul_apply, swap_apply_def, *, Ne.symm hea, Ne.symm heb, Ne.symm hec, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  by_cases hxb : x = b
  · subst x; simp [Perm.mul_apply, swap_apply_def, *, Ne.symm hea, Ne.symm heb, Ne.symm hec, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  by_cases hxc : x = c
  · subst x; simp [Perm.mul_apply, swap_apply_def, *, Ne.symm hea, Ne.symm heb, Ne.symm hec, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · simp [Perm.mul_apply, swap_apply_def, *, Ne.symm hea, Ne.symm heb, Ne.symm hec, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- Every internal 3-cycle is now separately supported on A(W), rather than
being synchronized across A,B,C. -/
theorem A_threeCycle_mem {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) (x y z : ZigzagLE r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    swap (endpointA x) (endpointA y) * swap (endpointA x) (endpointA z) ∈ BKgroup (r+2) := by
  obtain ⟨e,he,hstar⟩ := all_star_cycles hr h4 ih
  have hnot (w : ZigzagLE r) : e ≠ endpointA w := by
    intro hh
    apply he
    rw [hh]
    exact ⟨0,w,rfl⟩
  have hh := (BKgroup _).mul_mem (hstar x y hxy) (hstar z x hxz.symm)
  rwa [star_product e (endpointA x) (endpointA y) (endpointA z)
    (hnot x) (hnot y) (hnot z) ((endpointA_injective r).ne hxy)
    ((endpointA_injective r).ne hxz) ((endpointA_injective r).ne hyz)] at hh

#print axioms all_star_cycles
#print axioms A_threeCycle_mem
end Zigzag
```

### `FenceSupportedAlternating.lean`

```lean
import FenceSupportedCycles

namespace Zigzag
open Equiv Equiv.Perm

/-- Extend a smaller permutation by identity off the literal A fiber. -/
noncomputable def Aonly (r : ℕ) :
    Perm (ZigzagLE r) →* Perm (ZigzagLE (r+2)) := by
  classical
  exact Perm.ofSubtype.comp
    (Equiv.permCongrHom (Equiv.ofInjective (@endpointA r) (endpointA_injective r))).toMonoidHom

theorem Aonly_swap (r : ℕ) (x y : ZigzagLE r) :
    Aonly r (swap x y) = swap (endpointA x) (endpointA y) := by
  classical
  change Perm.ofSubtype ((Equiv.ofInjective (@endpointA r) (endpointA_injective r)).permCongr
    (swap x y)) = _
  rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans, Perm.ofSubtype_swap_eq]
  rfl

/-- The extension homomorphism has the specified action on every A-word. -/
theorem Aonly_apply (r : ℕ) (f : Perm (ZigzagLE r)) (w : ZigzagLE r) :
    Aonly r f (endpointA w) = endpointA (f w) := by
  classical
  let E := Equiv.ofInjective (@endpointA r) (endpointA_injective r)
  change Perm.ofSubtype (E.permCongr f) (endpointA w) = _
  have hE : (E w).val = endpointA w := rfl
  rw [← hE, Perm.ofSubtype_apply_coe]
  change (E (f (E.symm (E w)))).val = _
  rw [E.symm_apply_apply]
  rfl

theorem Aonly_fixed (r : ℕ) (f : Perm (ZigzagLE r)) (w : ZigzagLE (r+2))
    (hw : ¬ ∃ v, endpointA v = w) : Aonly r f w = w := by
  classical
  exact Perm.ofSubtype_apply_of_not_mem _ hw

/-- Source (10), now as a literal separately supported alternating action.
No hypotheses concerning support or sections remain. -/
theorem A_alternating_mem {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) (f : Perm (ZigzagLE r)) (hf : f ∈ alternatingGroup (ZigzagLE r)) :
    Aonly r f ∈ BKgroup (r+2) := by
  rw [← closure_three_cycles_eq_alternating] at hf
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    obtain ⟨x,hx⟩ := hf.isCycle.nonempty_support
    have hrepr := hf.eq_swap_mul_swap_iff_mem_support.mpr hx
    have hnodup := hf.nodup_iff_mem_support.mpr hx
    have hx1 : x ≠ f x := (mem_support.mp hx).symm
    have hx2 : x ≠ f (f x) := by
      have hn : x ≠ f x ∧ x ≠ f (f x) := by
        simpa using (List.nodup_cons.mp hnodup).1
      exact hn.2
    have hx3 : f x ≠ f (f x) := f.injective.ne hx1
    rw [hrepr, map_mul, Aonly_swap, Aonly_swap, swap_comm (endpointA x) (endpointA (f x))]
    exact A_threeCycle_mem hr h4 ih (f x) x (f (f x)) hx1.symm hx3 hx2
  | one => exact (Aonly r).map_one ▸ (BKgroup _).one_mem
  | mul f g _ _ hf hg => simpa only [map_mul] using (BKgroup _).mul_mem hf hg
  | inv f _ hf => simpa only [map_inv] using (BKgroup _).inv_mem hf

#print axioms Aonly_apply
#print axioms Aonly_fixed
#print axioms A_alternating_mem
end Zigzag
```

### `FenceBlockSaturation.lean`

```lean
import FenceSupportedAlternating

namespace Zigzag
open Equiv Equiv.Perm MulAction
open scoped Pointwise

/-- Any nontrivial BK block meeting A contains the whole A fiber. This uses
separate support, not merely transitivity of the diagonal action. -/
theorem block_A_saturated {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) (B : Set (ZigzagLE (r+2)))
    (hB : IsBlock (BKgroup (r+2)) B) (hBN : B.Nontrivial)
    (x : ZigzagLE r) (hx : endpointA x ∈ B) :
    ∀ w : ZigzagLE r, endpointA w ∈ B := by
  classical
  have hm := alternatingGroup.isMultiplyPretransitive (ZigzagLE r)
  have hc5 : 5 ≤ Nat.card (ZigzagLE r) := by
    simpa only [Nat.card_eq_fintype_card] using five_le_card r hr h4
  have htwo : IsMultiplyPretransitive
      (alternatingGroup (ZigzagLE r)) (ZigzagLE r) 2 :=
    isMultiplyPretransitive_of_le (by omega : 2 ≤ Nat.card (ZigzagLE r)-2)
      (by omega : Nat.card (ZigzagLE r)-2 ≤ Nat.card (ZigzagLE r))
  have : IsPretransitive (alternatingGroup (ZigzagLE r)) (ZigzagLE r) :=
    isPretransitive_of_is_two_pretransitive
  obtain ⟨y,hy,hyx⟩ := hBN.exists_ne (endpointA x)
  have preserved (f : alternatingGroup (ZigzagLE r))
      (u : ZigzagLE (r+2)) (hu : u ∈ B) (hfu : Aonly r f.val u = u) :
      ∀ v ∈ B, Aonly r f.val v ∈ B := by
    let g : BKgroup (r+2) := ⟨Aonly r f.val, A_alternating_mem hr h4 ih f.val f.property⟩
    have heq : g • B = B := hB.smul_eq_of_mem hu (by change Aonly r f.val u ∈ B; rw [hfu]; exact hu)
    intro v hv
    have hh : g • v ∈ g • B := Set.smul_mem_smul_set hv
    rw [heq] at hh
    exact hh
  intro w
  by_cases hwx : w = x
  · simpa only [hwx] using hx
  by_cases hyA : ∃ v, endpointA v = y
  · obtain ⟨v,rfl⟩ := hyA
    have hxv : x ≠ v := fun he => hyx (congrArg endpointA he.symm)
    obtain ⟨f,hfx,hfv⟩ := (is_two_pretransitive_iff.mp htwo) hxv (Ne.symm hwx)
    have hfix : Aonly r f.val (endpointA x) = endpointA x := by
      rw [Aonly_apply]; exact congrArg endpointA hfx
    have hh := preserved f (endpointA x) hx hfix (endpointA v) hy
    rw [Aonly_apply] at hh
    have hvw : f.val v = w := hfv
    rwa [hvw] at hh
  · obtain ⟨f,hfx⟩ := exists_smul_eq (M := alternatingGroup (ZigzagLE r)) x w
    have hh := preserved f y hy (Aonly_fixed r f.val y hyA) (endpointA x) hx
    rw [Aonly_apply] at hh
    have hxw : f.val x = w := hfx
    rwa [hxw] at hh

/-- Once a block contains A, every internal permutation preserves it. This is
the invariant-block interface needed for endpoint propagation. -/
theorem block_internal_invariant {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (B : Set (ZigzagLE (r+2))) (hB : IsBlock (BKgroup (r+2)) B)
    (hBA : ∀ w : ZigzagLE r, endpointA w ∈ B) (g : internalBK r) :
    (⟨g.val,internalBK_le r g.property⟩ : BKgroup (r+2)) • B = B := by
  obtain ⟨w⟩ : Nonempty (ZigzagLE r) := by
    have hc := five_le_card r hr h4
    exact Fintype.card_pos_iff.mp (by omega)
  apply hB.smul_eq_of_mem (hBA w)
  change g.val (endpointA w) ∈ B
  rw [show g.val (endpointA w) = endpointA (internalProjection r g w) from
    internalProjection_action g (frameA r) w]
  exact hBA _

#print axioms block_A_saturated
#print axioms block_internal_invariant
end Zigzag
```

### `LinearExtensionTransitivity.lean`

```lean
import ResidualRestriction
import FenceBoundarySwitch

namespace Zigzag
open Equiv

/-- Move a prescribed next letter leftwards through the unmatched suffix.
Every crossing is justified by the two literal extension inequalities. -/
private theorem bubble_next {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (v : LinearExtensions R) (k : Fin n) :
    ∀ j : ℕ, ∀ (w : LinearExtensions R),
      (∀ p : Fin n, p.val < k.val → w.val p = v.val p) →
      (hj : j < n) → k.val ≤ j → w.val ⟨j,hj⟩ = v.val k →
      ∃ g ∈ relationBK R,
        (∀ p : Fin n, p.val < k.val → (g w).val p = v.val p) ∧
        (g w).val k = v.val k := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro w hprefix hj hkj htarget
    by_cases he : j = k.val
    · refine ⟨1,(relationBK R).one_mem,hprefix,?_⟩
      change w.val k = v.val k
      have hk : (⟨j,hj⟩ : Fin n) = k := Fin.ext he
      exact (congrArg w.val hk.symm).trans htarget
    · have hpos : 0 < j := by omega
      let i := j-1
      have hi : i+1 < n := by dsimp [i]; omega
      let a : Fin n := leftPos i hi
      let b : Fin n := rightPos i hi
      have hb : b = ⟨j,hj⟩ := by apply Fin.ext; dsimp [b,rightPos,i]; omega
      have htarget' : w.val b = v.val k := hb ▸ htarget
      have hs : incomparable R i hi w.val := by
        constructor
        · intro hab
          rw [htarget'] at hab
          have hv := v.property _ _ hab
          have hp : (v.val.symm (w.val a)).val < k.val := by
            simpa only [v.val.symm_apply_apply,Fin.lt_def] using hv
          have hpre := hprefix (v.val.symm (w.val a)) hp
          rw [v.val.apply_symm_apply] at hpre
          have heq := w.val.injective hpre
          have hva := congrArg Fin.val heq
          change (v.val.symm (w.val a)).val = i at hva
          dsimp [i] at hva
          omega
        · intro hba
          have hw := w.property _ _ hba
          simp only [w.val.symm_apply_apply] at hw
          change i+1 < i at hw
          omega
      let w' := move R i hi w
      have hprefix' : ∀ p : Fin n, p.val < k.val → w'.val p = v.val p := by
        intro p hp
        change (move R i hi w).val p = _
        rw [move_at_other R i hi w p]
        · exact hprefix p hp
        · intro heq; have hp' := congrArg Fin.val heq
          change p.val = i at hp'
          dsimp [i] at hp'
          omega
        · intro heq; have hp' := congrArg Fin.val heq
          change p.val = i+1 at hp'
          dsimp [i] at hp'
          omega
      have ht' : w'.val a = v.val k :=
        (move_at_left R i hi w hs).trans htarget'
      obtain ⟨g,hg,hgp,hgt⟩ := ih i (by dsimp [i]; omega) w' hprefix' (by dsimp [i]; omega)
        (by dsimp [i]; omega) ht'
      refine ⟨g * move R i hi, (relationBK R).mul_mem hg (Subgroup.subset_closure ⟨i,hi,rfl⟩),hgp,hgt⟩

/-- Adjacent incomparable swaps connect the entire literal linear-extension
set, for every finite relation. No alternate model or poset theorem is assumed. -/
theorem relationBK_transitive {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (w v : LinearExtensions R) : ∃ g ∈ relationBK R, g w = v := by
  have build : ∀ k : ℕ, k ≤ n → ∃ g ∈ relationBK R,
      ∀ p : Fin n, p.val < k → (g w).val p = v.val p := by
    intro k hk
    induction k with
    | zero => exact ⟨1,(relationBK R).one_mem,fun _ hp => by omega⟩
    | succ k ih =>
      obtain ⟨g,hg,hgp⟩ := ih (by omega)
      let p : Fin n := ⟨k,by omega⟩
      let u := g w
      let q := u.val.symm (v.val p)
      have hq : k ≤ q.val := by
        by_contra h
        have hpq := hgp q (by omega)
        have hqv : u.val q = v.val p := u.val.apply_symm_apply _
        have heq := v.val.injective (hpq.symm.trans hqv)
        have hval := congrArg Fin.val heq
        change q.val = k at hval
        omega
      obtain ⟨f,hf,hfp,hft⟩ := bubble_next R v p q.val u hgp q.isLt hq
        (u.val.apply_symm_apply _)
      refine ⟨f*g,(relationBK R).mul_mem hf hg,?_⟩
      intro a ha
      by_cases hak : a.val < k
      · exact hfp a hak
      · have heq : a = p := Fin.ext (by dsimp [p]; omega)
        subst a
        exact hft
  obtain ⟨g,hg,hgp⟩ := build n le_rfl
  refine ⟨g,hg,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  exact hgp p p.isLt

#print axioms relationBK_transitive
end Zigzag
```

### `FenceFiberTransitivity.lean`

```lean
import LinearExtensionTransitivity
import ResidualWordFrames
import FenceBlockSaturation

namespace Zigzag
open Equiv MulAction
open scoped Pointwise

/-- Internal generators are transitive on each entire specified-first-and-last
fiber, including disconnected residual fences. -/
theorem internal_fiber_transitive {r : ℕ} (w v : ZigzagLE (r+2))
    (hf : w.val 0 = v.val 0)
    (hl : w.val (Fin.last (r+1)) = v.val (Fin.last (r+1))) :
    ∃ g : internalBK r, g.val w = v := by
  let F := ResidualFrame.ofWord w
  obtain ⟨u,hu⟩ := ResidualFrame.ofWord_covers w
  have hv : ∃ t, F.extension t = v := by
    exact F.exists_pad ⟨v, hf.symm.trans (ResidualFrame.ofWord_first w).symm,
      hl.symm.trans (ResidualFrame.ofWord_last w).symm⟩
  obtain ⟨t,ht⟩ := hv
  obtain ⟨f,hf,hft⟩ := relationBK_transitive F.relation u t
  obtain ⟨g,hg⟩ := F.restriction_surjective ⟨f,hf⟩
  refine ⟨g,?_⟩
  rw [← hu]
  change g.val (F.extension u) = v
  rw [F.restriction_action, hg]
  exact (congrArg F.extension hft).trans ht

/-- A block containing A absorbs any complete endpoint fiber it meets. -/
theorem block_absorbs_fiber {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (B : Set (ZigzagLE (r+2))) (hB : IsBlock (BKgroup (r+2)) B)
    (hBA : ∀ u : ZigzagLE r, endpointA u ∈ B) (w v : ZigzagLE (r+2))
    (hw : w ∈ B) (hf : w.val 0 = v.val 0)
    (hl : w.val (Fin.last (r+1)) = v.val (Fin.last (r+1))) : v ∈ B := by
  obtain ⟨g,hg⟩ := internal_fiber_transitive w v hf hl
  have hinv := block_internal_invariant hr h4 B hB hBA g
  have hh : (⟨g.val,internalBK_le r g.property⟩ : BKgroup (r+2)) • w ∈
      (⟨g.val,internalBK_le r g.property⟩ : BKgroup (r+2)) • B := Set.smul_mem_smul_set hw
  rw [hinv] at hh
  change g.val w ∈ B at hh
  rwa [hg] at hh

/-- The literal BK action is transitive, independently of the fence induction. -/
theorem BKgroup_transitive (n : ℕ) (w v : ZigzagLE n) :
    ∃ g ∈ BKgroup n, g w = v := relationBK_transitive (zigLt n) w v

#print axioms internal_fiber_transitive
#print axioms block_absorbs_fiber
#print axioms BKgroup_transitive
end Zigzag
```

### `PrimOrder.lean`

```lean
import FenceFiberTransitivity
import FiniteLinearExtension

namespace Zigzag
open Equiv

/-- Extend a priority compatible with the fence order. -/
theorem priority_extension {n : ℕ} (k : Fin n → ℕ)
    (hk : ∀ a b, zigLt n a b → k a ≤ k b) :
    ∃ w : ZigzagLE n, ∀ a b, k a < k b → w.val.symm a < w.val.symm b := by
  let R : Fin n → Fin n → Prop := fun a b =>
    k a < k b ∨ (k a = k b ∧ zigLt n a b)
  let : IsStrictOrder (Fin n) R := {
    irrefl a := by rintro (h | ⟨_,h⟩); omega; exact zigLt_irrefl n a h
    trans a b c hab hbc := by
      rcases hab with hab | ⟨hab,hab'⟩ <;> rcases hbc with hbc | ⟨hbc,hbc'⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨hab.trans hbc, zigLt_trans n a b c hab' hbc'⟩
  }
  have hex := finite_linear_extension (Fin n) R
  rw [Fintype.card_fin] at hex
  obtain ⟨w,hw⟩ := hex
  refine ⟨⟨w, ?_⟩, fun a b h => hw a b (Or.inl h)⟩
  intro a b hab
  have hh := hk a b hab
  exact hw a b (if he : k a = k b then Or.inr ⟨he,hab⟩ else Or.inl (by omega))

/-- A unique lowest-priority vertex is the first letter. -/
theorem priority_first {n : ℕ} (hn : 0 < n) (w : ZigzagLE n)
    (k : Fin n → ℕ) (hw : ∀ a b, k a < k b → w.val.symm a < w.val.symm b)
    (a : Fin n) (ha : ∀ b, b ≠ a → k a < k b) : w.val ⟨0,hn⟩ = a := by
  by_contra he
  have h := hw a _ (ha _ he)
  rw [w.val.symm_apply_apply] at h
  exact (Nat.not_lt_zero _ h)

/-- Prescribed three smallest priorities prescribe the first three letters. -/
theorem priority_prefix {n : ℕ} (hn : 3 ≤ n) (w : ZigzagLE n)
    (k : Fin n → ℕ) (hw : ∀ a b, k a < k b → w.val.symm a < w.val.symm b)
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ x, x ≠ a → k a < k x)
    (hb : ∀ x, x ≠ a → x ≠ b → k b < k x)
    (hc : ∀ x, x ≠ a → x ≠ b → x ≠ c → k c < k x) :
    w.val ⟨0,by omega⟩ = a ∧ w.val ⟨1,by omega⟩ = b ∧
      w.val ⟨2,by omega⟩ = c := by
  have h0 := priority_first (by omega) w k hw a ha
  have h1 : w.val ⟨1,by omega⟩ = b := by
    by_contra he
    have hna : w.val ⟨1,by omega⟩ ≠ a := by
      rw [← h0]; exact w.val.injective.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    have hh := hw b _ (hb _ hna he)
    rw [w.val.symm_apply_apply] at hh
    have hb0 : w.val.symm b = ⟨0,by omega⟩ := Fin.ext (by change (w.val.symm b).val < 1 at hh; change (w.val.symm b).val = 0; omega)
    have hh' := congrArg w.val hb0
    simp only [Equiv.apply_symm_apply, h0] at hh'
    exact hab hh'.symm
  refine ⟨h0,h1,?_⟩
  by_contra he
  have hna : w.val ⟨2,by omega⟩ ≠ a := by
    rw [← h0]; exact w.val.injective.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
  have hnb : w.val ⟨2,by omega⟩ ≠ b := by
    rw [← h1]; exact w.val.injective.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
  have hh := hw c _ (hc _ hna hnb he)
  rw [w.val.symm_apply_apply] at hh
  have hec : w.val.symm c = ⟨0,by omega⟩ ∨ w.val.symm c = ⟨1,by omega⟩ := by
    change (w.val.symm c).val < 2 at hh
    rcases (by omega : (w.val.symm c).val = 0 ∨ (w.val.symm c).val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hec with h | h
  · have hh' := congrArg w.val h
    simp only [Equiv.apply_symm_apply, h0] at hh'
    exact hac hh'.symm
  · have hh' := congrArg w.val h
    simp only [Equiv.apply_symm_apply, h1] at hh'
    exact hbc hh'.symm

/-- Reverse both vertex order and positions to reuse the prefix calculation. -/
theorem priority_suffix {n : ℕ} (hn : 3 ≤ n) (w : ZigzagLE n)
    (k : Fin n → ℕ) (hw : ∀ a b, k a < k b → w.val.symm a < w.val.symm b)
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc : ∀ x, x ≠ c → k x < k c)
    (hb : ∀ x, x ≠ c → x ≠ b → k x < k b)
    (ha : ∀ x, x ≠ c → x ≠ b → x ≠ a → k x < k a) :
    w.val ⟨n-3,by omega⟩ = a ∧ w.val ⟨n-2,by omega⟩ = b ∧
      w.val ⟨n-1,by omega⟩ = c := by
  have hlast : w.val ⟨n-1,by omega⟩ = c := by
    by_contra he
    have hh := hw _ c (hc _ he)
    rw [w.val.symm_apply_apply] at hh
    have := (w.val.symm c).isLt
    change n-1 < (w.val.symm c).val at hh
    omega
  have hmid : w.val ⟨n-2,by omega⟩ = b := by
    by_contra he
    have hnc : w.val ⟨n-2,by omega⟩ ≠ c := by
      rw [← hlast]; apply w.val.injective.ne; intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hh := hw _ b (hb _ hnc he)
    rw [w.val.symm_apply_apply] at hh
    have hbtop : w.val.symm b = ⟨n-1,by omega⟩ := Fin.ext (by
      have := (w.val.symm b).isLt; change n-2 < (w.val.symm b).val at hh; change (w.val.symm b).val = n-1; omega)
    have hh' := congrArg w.val hbtop
    simp only [Equiv.apply_symm_apply, hlast] at hh'
    exact hbc hh'
  refine ⟨?_,hmid,hlast⟩
  by_contra he
  have hnc : w.val ⟨n-3,by omega⟩ ≠ c := by
    rw [← hlast]; apply w.val.injective.ne; intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hnb : w.val ⟨n-3,by omega⟩ ≠ b := by
    rw [← hmid]; apply w.val.injective.ne; intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hh := hw _ a (ha _ hnc hnb he)
  rw [w.val.symm_apply_apply] at hh
  have hea : w.val.symm a = ⟨n-1,by omega⟩ ∨ w.val.symm a = ⟨n-2,by omega⟩ := by
    change n-3 < (w.val.symm a).val at hh
    have := (w.val.symm a).isLt
    rcases (by omega : (w.val.symm a).val = n-1 ∨ (w.val.symm a).val = n-2) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hea with h | h
  · have hh' := congrArg w.val h
    simp only [Equiv.apply_symm_apply, hlast] at hh'
    exact hac hh'
  · have hh' := congrArg w.val h
    simp only [Equiv.apply_symm_apply, hmid] at hh'
    exact hab hh'

#print axioms priority_extension
#print axioms priority_prefix
#print axioms priority_suffix
end Zigzag
```

### `PrimWitness.lean`

```lean
import PrimOrder

namespace Zigzag

/-- Fixed witness for the right endpoint braid, in the A endpoint fiber. -/
theorem prim_right_fixed_word {n : ℕ} (hn : 6 ≤ n) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨n-3,by omega⟩ = ⟨2,by omega⟩ ∧
      w.val ⟨n-2,by omega⟩ = ⟨3,by omega⟩ ∧
      w.val ⟨n-1,by omega⟩ = ⟨1,by omega⟩ := by
  let k : Fin n → ℕ := fun x =>
    if x.val = 0 then 0 else if x.val = 2 then 2 else
    if x.val = 3 then 3 else if x.val = 1 then 4 else 1
  have hk : ∀ a b, zigLt n a b → k a ≤ k b := by
    intro a b hab
    rcases hab with ⟨ha,hab⟩
    dsimp [k]; split_ifs <;> omega
  obtain ⟨w,hw⟩ := priority_extension k hk
  have hf := priority_first (by omega) w k hw ⟨0,by omega⟩ (by
    intro x hx; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    dsimp [k]; split_ifs <;> omega)
  have hs := priority_suffix (by omega : 3 ≤ n) w k hw
    ⟨2,by omega⟩ ⟨3,by omega⟩ ⟨1,by omega⟩
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro x hx; have : x.val ≠ 1 := fun h => hx (Fin.ext h); dsimp [k]; split_ifs <;> omega)
    (by intro x hx hy; have : x.val ≠ 1 := fun h => hx (Fin.ext h)
        have : x.val ≠ 3 := fun h => hy (Fin.ext h); dsimp [k]; split_ifs <;> omega)
    (by intro x hx hy hz; have : x.val ≠ 1 := fun h => hx (Fin.ext h)
        have : x.val ≠ 3 := fun h => hy (Fin.ext h)
        have : x.val ≠ 2 := fun h => hz (Fin.ext h); dsimp [k]; split_ifs <;> omega)
  exact ⟨w,hf,hs⟩

/-- Moving witnesses for every right endpoint, with three terminal maxima. -/
theorem prim_right_moving_word {n : ℕ} (hn : 6 ≤ n)
    (c b : Fin n) (hc : c.val % 2 = 1) (hb : b.val % 2 = 1)
    (hc1 : c.val ≠ 1) (hb1 : b.val ≠ 1) (hcb : c ≠ b) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨n-3,by omega⟩ = c ∧ w.val ⟨n-2,by omega⟩ = b ∧
      w.val ⟨n-1,by omega⟩ = ⟨1,by omega⟩ := by
  have hcb' : c.val ≠ b.val := fun h => hcb (Fin.ext h)
  let k : Fin n → ℕ := fun x => if x.val = 0 then 0 else
    if x = c then 2 else if x = b then 3 else if x.val = 1 then 4 else 1
  have hk : ∀ a b, zigLt n a b → k a ≤ k b := by
    intro a d had
    rcases had with ⟨ha,had⟩
    dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff]
  obtain ⟨w,hw⟩ := priority_extension k hk
  have hf := priority_first (by omega) w k hw ⟨0,by omega⟩ (by
    intro x hx; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
  have hs := priority_suffix (by omega : 3 ≤ n) w k hw c b ⟨1,by omega⟩ hcb
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro x hx; have : x.val ≠ 1 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
    (by intro x hx hy; have : x.val ≠ 1 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
    (by intro x hx hy hz; have : x.val ≠ 1 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
  exact ⟨w,hf,hs⟩

/-- Fixed witness for the left endpoint braid, beginning with vertex zero. -/
theorem prim_left_fixed_word {n : ℕ} (hn : 6 ≤ n) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨1,by omega⟩ = ⟨2,by omega⟩ ∧
      w.val ⟨2,by omega⟩ = ⟨1,by omega⟩ := by
  let k : Fin n → ℕ := fun x =>
    if x.val = 0 then 0 else if x.val = 2 then 1 else if x.val = 1 then 2 else 3
  have hk : ∀ a b, zigLt n a b → k a ≤ k b := by
    intro a b hab; rcases hab with ⟨ha,hab⟩
    dsimp [k]; split_ifs <;> omega
  obtain ⟨w,hw⟩ := priority_extension k hk
  refine ⟨w, priority_prefix (by omega) w k hw ⟨0,by omega⟩ ⟨2,by omega⟩ ⟨1,by omega⟩
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega) ?_ ?_ ?_⟩
  · intro x hx; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    dsimp [k]; split_ifs <;> omega
  · intro x hx hy; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    have : x.val ≠ 2 := fun h => hy (Fin.ext h)
    dsimp [k]; split_ifs <;> omega
  · intro x hx hy hz; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    have : x.val ≠ 2 := fun h => hy (Fin.ext h)
    have : x.val ≠ 1 := fun h => hz (Fin.ext h)
    dsimp [k]; split_ifs <;> omega

/-- Moving witnesses for every pair of endpoints. -/
theorem prim_left_moving_word {n : ℕ} (hn : 6 ≤ n)
    (a b c : Fin n) (ha : a.val % 2 = 0) (hb : b.val % 2 = 0)
    (hc : c.val % 2 = 1) (ha0 : a.val ≠ 0) (hb0 : b.val ≠ 0) (hab : a ≠ b) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨1,by omega⟩ = b ∧ w.val ⟨2,by omega⟩ = a ∧
      w.val ⟨n-1,by omega⟩ = c := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  let k : Fin n → ℕ := fun x => if x.val = 0 then 0 else
    if x = b then 1 else if x = a then 2 else if x = c then 4 else 3
  have hk : ∀ x y, zigLt n x y → k x ≤ k y := by
    intro x y hxy; rcases hxy with ⟨hx,hxy⟩
    dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  obtain ⟨w,hw⟩ := priority_extension k hk
  have hp := priority_prefix (by omega : 3 ≤ n) w k hw ⟨0,by omega⟩ b a
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega) hab.symm
    (by intro x hx; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
    (by intro x hx hy; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
    (by intro x hx hy hz; have : x.val ≠ 0 := fun h => hx (Fin.ext h)
        dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
  have hl : w.val ⟨n-1,by omega⟩ = c := by
    by_contra he
    have hh := hw (w.val ⟨n-1,by omega⟩) c (by
      dsimp [k]; split_ifs <;> simp_all [Fin.ext_iff])
    rw [w.val.symm_apply_apply] at hh
    have := (w.val.symm c).isLt
    change n-1 < (w.val.symm c).val at hh
    omega
  exact ⟨w,hp.1,hp.2.1,hp.2.2,hl⟩

#print axioms prim_right_fixed_word
#print axioms prim_right_moving_word
#print axioms prim_left_fixed_word
#print axioms prim_left_moving_word
end Zigzag
```

### `PrimBraid.lean`

```lean
import PrimWitness

namespace Zigzag
open Equiv

/-- A legal literal swap. -/
theorem prim_move_raw {n : ℕ} (i : ℕ) (hi : i+1<n) (w : ZigzagLE n)
    (h : (w.val (leftPos i hi)).val % 2 = (w.val (rightPos i hi)).val % 2) :
    (bk n i hi w).val = rawSwap i hi w.val := by
  have hs : incomparable (zigLt n) i hi w.val := same_parity_incomparable _ _ h
  rw [show (bk n i hi w).val = _ from move_apply _ i hi w, ite_eq_left hs]


/-- Arithmetic evaluation of the adjacent position swap. -/
theorem prim_swap_val {n : ℕ} (i : ℕ) (hi : i+1<n) (p : Fin n) :
    (adjacentSwap i hi p).val =
      if p.val = i then i+1 else if p.val = i+1 then i else p.val := by
  by_cases hp : p.val = i
  · have he : p = leftPos i hi := Fin.ext hp
    rw [he, show adjacentSwap i hi (leftPos i hi) = rightPos i hi from Equiv.swap_apply_left _ _]
    simp [leftPos,rightPos]
  · by_cases hq : p.val = i+1
    · have he : p = rightPos i hi := Fin.ext hq
      rw [he, show adjacentSwap i hi (rightPos i hi) = leftPos i hi from Equiv.swap_apply_right _ _]
      simp [leftPos,rightPos]
    · have he : adjacentSwap i hi p = p := Equiv.swap_apply_of_ne_of_ne
        (fun h => hp (congrArg Fin.val h)) (fun h => hq (congrArg Fin.val h))
      rw [he, ite_eq_right hp, ite_eq_right hq]

theorem prim_rightPos_end {n : ℕ} (hn : 3 ≤ n) (hi : n-2+1<n) :
    rightPos (n-2) hi = (⟨n-1,by omega⟩ : Fin n) :=
  Fin.ext (by dsimp [rightPos]; omega)

/-- A same-parity adjacent swap preserves the parity at every position. -/
theorem prim_move_parity {n : ℕ} (i : ℕ) (hi : i+1<n) (w : ZigzagLE n)
    (h : (w.val (leftPos i hi)).val % 2 = (w.val (rightPos i hi)).val % 2)
    (p : Fin n) : ( (bk n i hi w).val p).val % 2 = (w.val p).val % 2 := by
  rw [prim_move_raw i hi w h]
  simp only [rawSwap, Equiv.trans_apply, adjacentSwap, Equiv.swap_apply_def]
  split_ifs with hq hp
  · subst p; exact h.symm
  · subst p; exact h
  · rfl

/-- Three legal same-parity swaps evaluate as their position permutation. -/
theorem prim_braid_raw {n : ℕ} (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
    (w : ZigzagLE n)
    (hs : (w.val (leftPos i hi)).val % 2 = (w.val (rightPos i hi)).val % 2)
    (ht : (w.val (leftPos j hj)).val % 2 = (w.val (rightPos j hj)).val % 2)
    (p : Fin n) :
    ((bk n i hi * bk n j hj * bk n i hi) w).val p =
      w.val (adjacentSwap i hi (adjacentSwap j hj (adjacentSwap i hi p))) := by
  have ht' : (((bk n i hi) w).val (leftPos j hj)).val % 2 =
      (((bk n i hi) w).val (rightPos j hj)).val % 2 := by
    rw [prim_move_parity i hi w hs, prim_move_parity i hi w hs]; exact ht
  have hs' : (((bk n j hj) ((bk n i hi) w)).val (leftPos i hi)).val % 2 =
      (((bk n j hj) ((bk n i hi) w)).val (rightPos i hi)).val % 2 := by
    rw [prim_move_parity j hj _ ht', prim_move_parity j hj _ ht',
      prim_move_parity i hi w hs, prim_move_parity i hi w hs]; exact hs
  change (bk n i hi (bk n j hj (bk n i hi w))).val p = _
  rw [prim_move_raw i hi _ hs']
  change (bk n j hj (bk n i hi w)).val (adjacentSwap i hi p) = _
  rw [prim_move_raw j hj _ ht']
  change (bk n i hi w).val (adjacentSwap j hj (adjacentSwap i hi p)) = _
  rw [prim_move_raw i hi w hs]
  rfl

/-- Conjugating a middle move which fixes the swapped word fixes the word. -/
theorem prim_braid_fixed {n : ℕ} (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
    (w : ZigzagLE n)
    (h : ¬ incomparable (zigLt n) j hj (bk n i hi w).val) :
    (bk n i hi * bk n j hj * bk n i hi) w = w := by
  have ht : bk n j hj (bk n i hi w) = bk n i hi w := by
    apply Subtype.ext
    rw [show (bk n j hj (bk n i hi w)).val = _ from move_apply _ j hj _, ite_eq_right h]
  change bk n i hi (bk n j hj (bk n i hi w)) = w
  rw [ht]
  exact move_involutive _ i hi w

/-- The right source braid t_(n-1)t_(n-2)t_(n-1). -/
def primRight (n : ℕ) (hn : 3 ≤ n) : Perm (ZigzagLE n) :=
  bk n (n-2) (by omega) * bk n (n-3) (by omega) * bk n (n-2) (by omega)
/-- The left source braid t_1 t_2 t_1. -/
def primLeft (n : ℕ) (hn : 3 ≤ n) : Perm (ZigzagLE n) :=
  bk n 0 (by omega) * bk n 1 (by omega) * bk n 0 (by omega)

theorem primRight_mem (n : ℕ) (hn : 3 ≤ n) : primRight n hn ∈ BKgroup n :=
  (BKgroup n).mul_mem ((BKgroup n).mul_mem (bk_mem _ _ _) (bk_mem _ _ _)) (bk_mem _ _ _)
theorem primLeft_mem (n : ℕ) (hn : 3 ≤ n) : primLeft n hn ∈ BKgroup n :=
  (BKgroup n).mul_mem ((BKgroup n).mul_mem (bk_mem _ _ _) (bk_mem _ _ _)) (bk_mem _ _ _)

/-- Fixed A point for the right braid. -/
theorem primRight_fixed {n : ℕ} (hn : 6 ≤ n) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨n-1,by omega⟩ = ⟨1,by omega⟩ ∧ primRight n (by omega) w = w := by
  obtain ⟨w,h0,h2,h3,h1⟩ := prim_right_fixed_word hn
  refine ⟨w,h0,h1,prim_braid_fixed _ _ _ _ w ?_⟩
  have hs : (w.val (leftPos (n-2) (by omega))).val % 2 =
      (w.val (rightPos (n-2) (by omega))).val % 2 := by
    rw [prim_rightPos_end (by omega)]
    change (w.val ⟨n-2,by omega⟩).val % 2 = (w.val ⟨n-1,by omega⟩).val % 2
    rw [h3,h1]; norm_num
  have he0 : (bk n (n-2) (by omega) w).val (leftPos (n-3) (by omega)) = ⟨2,by omega⟩ := by
    rw [prim_move_raw _ _ w hs]
    change w.val (adjacentSwap (n-2) _ ⟨n-3,by omega⟩) = _
    rw [show adjacentSwap (n-2) (by omega : n-2+1<n) ⟨n-3,by omega⟩ = ⟨n-3,by omega⟩ from
      Equiv.swap_apply_of_ne_of_ne (by intro h; have := congrArg Fin.val h; dsimp [leftPos] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [rightPos] at this; omega)]
    exact h2
  have he1 : (bk n (n-2) (by omega) w).val (rightPos (n-3) (by omega)) = ⟨1,by omega⟩ := by
    have hh := move_at_left (zigLt n) (n-2) (by omega) w (same_parity_incomparable _ _ hs)
    rw [prim_rightPos_end (by omega)] at hh
    have he : rightPos (n-3) (by omega : n-3+1<n) = leftPos (n-2) (by omega : n-2+1<n) := Fin.ext (by dsimp [leftPos,rightPos]; omega)
    rw [he]; exact hh.trans h1
  intro h
  apply h.1
  rw [he0,he1]
  exact ⟨by norm_num, Or.inr rfl⟩

/-- Fixed point beginning with zero for the left braid. -/
theorem primLeft_fixed {n : ℕ} (hn : 6 ≤ n) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      primLeft n (by omega) w = w := by
  obtain ⟨w,h0,h2,h1⟩ := prim_left_fixed_word hn
  refine ⟨w,h0,prim_braid_fixed _ _ _ _ w ?_⟩
  have hs : incomparable (zigLt n) 0 (by omega) w.val := by
    apply same_parity_incomparable
    change (w.val ⟨0,by omega⟩).val % 2 = (w.val ⟨1,by omega⟩).val % 2
    rw [h0,h2]; norm_num
  have he0 : (bk n 0 (by omega) w).val (leftPos 1 (by omega)) = ⟨0,by omega⟩ :=
    (move_at_right _ 0 (by omega) w hs).trans h0
  have he1 : (bk n 0 (by omega) w).val (rightPos 1 (by omega)) = ⟨1,by omega⟩ := by
    have he := move_at_other (zigLt n) 0 (by omega) w (rightPos 1 (by omega))
      (by intro h; have := congrArg Fin.val h; change 2 = 0 at this; omega)
      (by intro h; have := congrArg Fin.val h; change 2 = 1 at this; omega)
    exact he.trans h1
  intro h; apply h.1
  rw [he0,he1]
  exact ⟨by norm_num, Or.inl rfl⟩

/-- Moving the rightmost triple of maxima reaches the requested last vertex. -/
theorem primRight_moving {n : ℕ} (hn : 6 ≤ n)
    (c b : Fin n) (hc : c.val % 2 = 1) (hb : b.val % 2 = 1)
    (hc1 : c.val ≠ 1) (hb1 : b.val ≠ 1) (hcb : c ≠ b) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨n-1,by omega⟩ = ⟨1,by omega⟩ ∧
      (primRight n (by omega) w).val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      (primRight n (by omega) w).val ⟨n-1,by omega⟩ = c := by
  obtain ⟨w,h0,hc',hb',h1⟩ := prim_right_moving_word hn c b hc hb hc1 hb1 hcb
  have hs : (w.val (leftPos (n-2) (by omega))).val % 2 =
      (w.val (rightPos (n-2) (by omega))).val % 2 := by
    rw [prim_rightPos_end (by omega)]
    change (w.val ⟨n-2,by omega⟩).val % 2 = (w.val ⟨n-1,by omega⟩).val % 2
    rw [hb',h1]; exact hb
  have ht : (w.val (leftPos (n-3) (by omega))).val % 2 =
      (w.val (rightPos (n-3) (by omega))).val % 2 := by
    have he : rightPos (n-3) (by omega : n-3+1<n) = (⟨n-2,by omega⟩ : Fin n) := Fin.ext (by dsimp [rightPos]; omega)
    rw [he]; change (w.val ⟨n-3,by omega⟩).val % 2 = _
    rw [hc',hb',hc,hb]
  refine ⟨w,h0,h1,?_,?_⟩
  · rw [primRight, prim_braid_raw _ _ _ _ w hs ht]
    convert h0 using 1
    congr 1
    apply Fin.ext
    simp only [prim_swap_val]
    split_ifs <;> first | contradiction | omega
  · rw [primRight, prim_braid_raw _ _ _ _ w hs ht]
    convert hc' using 1
    congr 1
    apply Fin.ext
    simp only [prim_swap_val]
    split_ifs <;> first | contradiction | omega

/-- Moving the leftmost triple of minima reaches the requested first vertex. -/
theorem primLeft_moving {n : ℕ} (hn : 6 ≤ n)
    (a b c : Fin n) (ha : a.val % 2 = 0) (hb : b.val % 2 = 0)
    (hc : c.val % 2 = 1) (ha0 : a.val ≠ 0) (hb0 : b.val ≠ 0) (hab : a ≠ b) :
    ∃ w : ZigzagLE n, w.val ⟨0,by omega⟩ = ⟨0,by omega⟩ ∧
      w.val ⟨n-1,by omega⟩ = c ∧
      (primLeft n (by omega) w).val ⟨0,by omega⟩ = a ∧
      (primLeft n (by omega) w).val ⟨n-1,by omega⟩ = c := by
  obtain ⟨w,h0,hb',ha',hc'⟩ := prim_left_moving_word hn a b c ha hb hc ha0 hb0 hab
  have hs : (w.val (leftPos 0 (by omega))).val % 2 =
      (w.val (rightPos 0 (by omega))).val % 2 := by
    change (w.val ⟨0,by omega⟩).val % 2 = (w.val ⟨1,by omega⟩).val % 2
    rw [h0,hb']; exact hb.symm
  have ht : (w.val (leftPos 1 (by omega))).val % 2 =
      (w.val (rightPos 1 (by omega))).val % 2 := by
    change (w.val ⟨1,by omega⟩).val % 2 = (w.val ⟨2,by omega⟩).val % 2
    rw [hb',ha',hb,ha]
  refine ⟨w,h0,hc',?_,?_⟩
  · rw [primLeft, prim_braid_raw _ _ _ _ w hs ht]
    convert ha' using 1
    congr 1
  · rw [primLeft, prim_braid_raw _ _ _ _ w hs ht]
    convert hc' using 1
    congr 1
    apply Fin.ext
    simp only [prim_swap_val]
    split_ifs <;> first | contradiction | omega

#print axioms prim_braid_raw
#print axioms primRight_fixed
#print axioms primLeft_fixed
end Zigzag
```

### `PrimBlock.lean`

```lean
import PrimBraid

namespace Zigzag
open Equiv MulAction
open scoped Pointwise

/-- A fixed point in a block forces the entire block to be invariant. -/
theorem prim_block_move {n : ℕ} (B : Set (ZigzagLE n))
    (hB : IsBlock (BKgroup n) B) (g : Perm (ZigzagLE n)) (hg : g ∈ BKgroup n)
    (x : ZigzagLE n) (hx : x ∈ B) (hfix : g x = x) :
    ∀ w ∈ B, g w ∈ B := by
  let g' : BKgroup n := ⟨g,hg⟩
  have heq : g' • B = B := hB.smul_eq_of_mem hx (by change g x ∈ B; rwa [hfix])
  intro w hw
  have hh : g' • w ∈ g' • B := Set.smul_mem_smul_set hw
  rw [heq] at hh
  exact hh

/-- A block containing A contains every word beginning with zero. -/
theorem prim_block_first_zero {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (B : Set (ZigzagLE (r+2))) (hB : IsBlock (BKgroup (r+2)) B)
    (hBA : ∀ w : ZigzagLE r, endpointA w ∈ B)
    (v : ZigzagLE (r+2)) (hv : v.val 0 = 0) : v ∈ B := by
  have inA (w : ZigzagLE (r+2)) (hf : w.val 0 = 0)
      (hl : w.val (Fin.last (r+1)) = 1) : w ∈ B := by
    obtain ⟨u,rfl⟩ := (endpointA_range_iff w).mpr ⟨hf,hl⟩
    exact hBA u
  obtain ⟨x,hx0,hx1,hfix⟩ := primRight_fixed (by omega : 6 ≤ r+2)
  have hx : x ∈ B := inA x hx0 hx1
  have hinv := prim_block_move B hB _ (primRight_mem (r+2) (by omega)) x hx hfix
  let c := v.val (Fin.last (r+1))
  by_cases hc1 : c.val = 1
  · exact inA v hv (Fin.ext hc1)
  have hc : c.val % 2 = 1 := by
    have hn : Even (r+2) := hr.add (by decide : Even 2)
    exact last_vertex_odd hn (by omega) v
  let b : Fin (r+2) := if c.val = 3 then ⟨5,by omega⟩ else ⟨3,by omega⟩
  have hb : b.val % 2 = 1 := by dsimp [b]; split_ifs <;> norm_num
  have hb1 : b.val ≠ 1 := by dsimp [b]; split_ifs <;> norm_num
  have hcb : c ≠ b := by
    dsimp [b]; split_ifs <;> intro h <;> have := congrArg Fin.val h <;> dsimp at this <;> omega
  obtain ⟨w,hw0,hw1,hw0',hwc⟩ := primRight_moving (by omega : 6 ≤ r+2) c b hc hb hc1 hb1 hcb
  have hw : w ∈ B := inA w hw0 hw1
  apply block_absorbs_fiber hr h4 B hB hBA (primRight (r+2) (by omega) w) v (hinv w hw)
  · exact hw0'.trans hv.symm
  · exact hwc

/-- Endpoint braid propagation fills every endpoint fiber. -/
theorem block_containing_A_full {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (_ih : BKgroup r = ⊤) (B : Set (ZigzagLE (r+2)))
    (hB : IsBlock (BKgroup (r+2)) B)
    (hBA : ∀ w : ZigzagLE r, endpointA w ∈ B) : B = Set.univ := by
  have hzero := prim_block_first_zero hr h4 B hB hBA
  obtain ⟨x,hx0,hfix⟩ := primLeft_fixed (by omega : 6 ≤ r+2)
  have hinv := prim_block_move B hB _ (primLeft_mem (r+2) (by omega)) x (hzero x hx0) hfix
  apply Set.eq_univ_of_forall
  intro v
  let a := v.val 0
  let c := v.val (Fin.last (r+1))
  by_cases ha0 : a.val = 0
  · exact hzero v (Fin.ext ha0)
  have ha : a.val % 2 = 0 := first_vertex_even (by omega) v
  have hc : c.val % 2 = 1 := last_vertex_odd (hr.add (by decide : Even 2)) (by omega) v
  let b : Fin (r+2) := if a.val = 2 then ⟨4,by omega⟩ else ⟨2,by omega⟩
  have hb : b.val % 2 = 0 := by dsimp [b]; split_ifs <;> norm_num
  have hb0 : b.val ≠ 0 := by dsimp [b]; split_ifs <;> norm_num
  have hab : a ≠ b := by
    dsimp [b]; split_ifs <;> intro h <;> have := congrArg Fin.val h <;> dsimp at this <;> omega
  obtain ⟨w,hw0,hwc,hwa',hwc'⟩ := primLeft_moving (by omega : 6 ≤ r+2) a b c ha hb hc ha0 hb0 hab
  apply block_absorbs_fiber hr h4 B hB hBA (primLeft (r+2) (by omega) w) v (hinv w (hzero w hw0))
  · exact hwa'
  · exact hwc'

#print axioms prim_block_first_zero
#print axioms block_containing_A_full
end Zigzag
```

### `PrimAlternatingStep.lean`

```lean
import PrimBlock
import GroupSkeleton

namespace Zigzag
open Equiv Equiv.Perm MulAction

/-- The literal BK action is primitive under the smaller symmetric-group
induction hypothesis. -/
theorem prim_BKgroup_preprimitive {r : ℕ} (hr : Even r) (h4 : 4 ≤ r)
    (ih : BKgroup r = ⊤) : IsPreprimitive (BKgroup (r+2)) (ZigzagLE (r+2)) := by
  have : IsPretransitive (BKgroup (r+2)) (ZigzagLE (r+2)) := ⟨fun w v => by
    obtain ⟨g,hg,hgv⟩ := BKgroup_transitive (r+2) w v
    exact ⟨⟨g,hg⟩,hgv⟩⟩
  obtain ⟨u⟩ : Nonempty (ZigzagLE r) := by
    have hc := five_le_card r hr h4
    exact Fintype.card_pos_iff.mp (by omega)
  apply IsPreprimitive.of_isTrivialBlock_base (endpointA u)
  intro B hx hB
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  · apply Or.inr
    exact block_containing_A_full hr h4 ih B hB
      (block_A_saturated hr h4 ih B hB (Set.not_subsingleton_iff.mp hs) u hx)

/-- Unconditional alternating induction step on the source's extension set. -/
theorem alternatingStep_proved : AlternatingStep := by
  intro n hn h6 ih
  have hr : Even (n-2) := by obtain ⟨k,hk⟩ := hn; exact ⟨k-1,by omega⟩
  have hp := prim_BKgroup_preprimitive hr (by omega : 4 ≤ n-2) ih
  have he : n-2+2 = n := by omega
  rw [he] at hp
  obtain ⟨g,hg,h3⟩ := threeCycle_step n hn h6 ih
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hp h3 hg

#print AlternatingStep
#check @block_containing_A_full
#check @prim_BKgroup_preprimitive
#check @alternatingStep_proved
#print axioms prim_BKgroup_preprimitive
#print axioms alternatingStep_proved
end Zigzag
```

### `OddLocality.lean`

```lean
import ZigzagDefinitions

set_option linter.unusedSimpArgs false

namespace Zigzag
open Equiv

/-- A local move leaves every other position unchanged. -/
theorem odd_move_outside {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i + 1 < n) (w : LinearExtensions R) (a : Fin n)
    (ha : a.val ≠ i) (hb : a.val ≠ i + 1) :
    (move R i hi w).val a = w.val a := by
  rw [move_apply]
  split_ifs
  · change w.val (adjacentSwap i hi a) = w.val a
    rw [adjacentSwap, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => ha (congrArg Fin.val h)
    · exact fun h => hb (congrArg Fin.val h)
  · rfl

/-- The incomparability decision at a separated pair is unchanged. -/
theorem odd_incomparable_move {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 1 < j)
    (w : LinearExtensions R) :
    incomparable R j hj (move R i hi w).val ↔ incomparable R j hj w.val := by
  unfold incomparable
  rw [odd_move_outside R i hi w _ (by dsimp [leftPos]; omega)
      (by dsimp [leftPos]; omega),
    odd_move_outside R i hi w _ (by dsimp [rightPos]; omega)
      (by dsimp [rightPos]; omega)]

theorem odd_incomparable_move_left {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 1 < j)
    (w : LinearExtensions R) :
    incomparable R i hi (move R j hj w).val ↔ incomparable R i hi w.val := by
  unfold incomparable
  rw [odd_move_outside R j hj w _ (by dsimp [leftPos]; omega)
      (by dsimp [leftPos]; omega),
    odd_move_outside R j hj w _ (by dsimp [rightPos]; omega)
      (by dsimp [rightPos]; omega)]

/-- Disjoint adjacent swaps commute on literal words. -/
theorem odd_rawSwap_commute {n : ℕ} (i j : ℕ) (hi : i + 1 < n)
    (hj : j + 1 < n) (hij : i + 1 < j) (w : Perm (Fin n)) :
    rawSwap i hi (rawSwap j hj w) = rawSwap j hj (rawSwap i hi w) := by
  apply Equiv.ext
  intro a
  change w (adjacentSwap j hj (adjacentSwap i hi a)) =
    w (adjacentSwap i hi (adjacentSwap j hj a))
  have h1 : leftPos i hi ≠ leftPos j hj := by simp only [ne_eq, Fin.ext_iff, leftPos]; omega
  have h2 : leftPos i hi ≠ rightPos j hj := by simp only [ne_eq, Fin.ext_iff, leftPos, rightPos]; omega
  have h3 : rightPos i hi ≠ leftPos j hj := by simp only [ne_eq, Fin.ext_iff, leftPos, rightPos]; omega
  have h4 : rightPos i hi ≠ rightPos j hj := by simp only [ne_eq, Fin.ext_iff, rightPos]; omega
  have h0 : leftPos i hi ≠ rightPos i hi := by simp only [ne_eq, Fin.ext_iff, leftPos, rightPos]; omega
  have h5 : leftPos j hj ≠ rightPos j hj := by simp only [ne_eq, Fin.ext_iff, leftPos, rightPos]; omega
  by_cases ha : a = leftPos i hi
  · subst a; simp [adjacentSwap, Equiv.swap_apply_def, h0, h1, h2, h3, h4, h5, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  by_cases hb : a = rightPos i hi
  · subst a; simp [adjacentSwap, Equiv.swap_apply_def, h0, h1, h2, h3, h4, h5, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  by_cases hc : a = leftPos j hj
  · subst a; simp [adjacentSwap, Equiv.swap_apply_def, h0, h1, h2, h3, h4, h5, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  by_cases hd : a = rightPos j hj
  · subst a; simp [adjacentSwap, Equiv.swap_apply_def, h0, h1, h2, h3, h4, h5, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  simp [adjacentSwap, Equiv.swap_apply_of_ne_of_ne, ha, hb, hc, hd]

/-- Literal BK moves at separated position pairs commute. -/
theorem odd_move_commute {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 1 < j)
    (w : LinearExtensions R) :
    move R i hi (move R j hj w) = move R j hj (move R i hi w) := by
  apply Subtype.ext
  rw [move_apply R i hi (move R j hj w), move_apply R j hj (move R i hi w)]
  rw [if_congr (odd_incomparable_move_left R i j hi hj hij w) rfl rfl,
    if_congr (odd_incomparable_move R i j hi hj hij w) rfl rfl]
  rw [move_apply, move_apply]
  split_ifs <;> try rfl
  exact odd_rawSwap_commute i j hi hj hij w.val

#print axioms odd_move_outside
#print axioms odd_move_commute
end Zigzag
```

### `OddSignPairing.lean`

```lean
import Mathlib.GroupTheory.Perm.Sign

namespace Zigzag
open Equiv Equiv.Perm

/-- Sign splits over any invariant predicate. -/
theorem odd_sign_partition {α : Type*} [Fintype α] [DecidableEq α]
    (s : Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (s x) ↔ p x) :
    sign s = sign (s.subtypePerm hp) *
      sign (s.subtypePerm (p := fun x => ¬p x) (fun x => not_congr (hp x))) := by
  let a := s.subtypePerm hp
  let b := s.subtypePerm (p := fun x => ¬p x) (fun x => not_congr (hp x))
  have he : a.subtypeCongr b = s := by
    ext x
    by_cases hx : p x
    · rw [Perm.subtypeCongr.left_apply _ _ hx]; rfl
    · rw [Perm.subtypeCongr.right_apply _ _ hx]; rfl
  exact (congrArg sign he).symm.trans (sign_subtypeCongr a b)

/-- A permutation on paired copies has positive sign. The pairing need only
intertwine the permutation and exchange the two invariant pieces. -/
theorem odd_sign_paired {α : Type*} [Fintype α] [DecidableEq α]
    (s : Perm α) (q : α → Prop) [DecidablePred q]
    (hq : ∀ x, q (s x) ↔ q x)
    (e : {x // q x} ≃ {x // ¬q x})
    (he : ∀ x, e (s.subtypePerm hq x) =
      s.subtypePerm (p := fun x => ¬q x) (fun x => not_congr (hq x)) (e x)) : sign s = 1 := by
  rw [odd_sign_partition s q hq]
  have h := sign_eq_sign_of_equiv _ _ e he
  rw [h, Int.units_mul_self]

/-- Cancel two paired pieces outside an invariant distinguished set. -/
theorem odd_sign_cancel {α : Type*} [Fintype α] [DecidableEq α]
    (s : Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (s x) ↔ p x)
    (q : {x // ¬p x} → Prop) [DecidablePred q]
    (hq : ∀ x, q (s.subtypePerm (p := fun x => ¬p x) (fun x => not_congr (hp x)) x) ↔ q x)
    (e : {x : {x // ¬p x} // q x} ≃ {x : {x // ¬p x} // ¬q x})
    (he : ∀ x, e ((s.subtypePerm (p := fun x => ¬p x) (fun x => not_congr (hp x))).subtypePerm hq x) =
      (s.subtypePerm (p := fun x => ¬p x) (fun x => not_congr (hp x))).subtypePerm
        (fun x => not_congr (hq x)) (e x)) :
    sign s = sign (s.subtypePerm hp) := by
  rw [odd_sign_partition s p hp, odd_sign_paired _ q hq e he, mul_one]

#print axioms odd_sign_partition
#print axioms odd_sign_paired
#print axioms odd_sign_cancel
end Zigzag
```

### `OddCancellation.lean`

```lean
import OddLocality
import OddSignPairing

namespace Zigzag
open Equiv Equiv.Perm

/-- On its moving piece a literal move exchanges its two entries. -/
theorem odd_move_pair {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i+1<n) (w : LinearExtensions R)
    (h : incomparable R i hi w.val) :
    (move R i hi w).val (leftPos i hi) = w.val (rightPos i hi) ∧
    (move R i hi w).val (rightPos i hi) = w.val (leftPos i hi) := by
  rw [move_apply]
  simp only [h, ite_true]
  simp [rawSwap, adjacentSwap]

theorem odd_incomparable_self {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i : ℕ) (hi : i+1<n) (w : LinearExtensions R) :
    incomparable R i hi (move R i hi w).val ↔ incomparable R i hi w.val := by
  by_cases h : incomparable R i hi w.val
  · have hv := odd_move_pair R i hi w h
    simp only [incomparable, hv.1, hv.2]
    exact and_comm
  · have hv : move R i hi w = w := by apply Subtype.ext; simp [move_apply, h]
    rw [hv]

/-- Swapping a separated pair cancels all sign contributions outside its
comparable (fixed) piece. This applies to any finite relation. -/
theorem odd_sign_cancel_separated {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (i j : ℕ) (hi : i+1<n) (hj : j+1<n) (hij : i+1<j) :
    sign (move R i hi) =
      sign ((move R i hi).subtypePerm (p := fun w => ¬incomparable R j hj w.val)
        (fun w => not_congr (odd_incomparable_move R i j hi hj hij w))) := by
  classical
  let s := move R i hi
  let t := move R j hj
  let p := fun w : LinearExtensions R => ¬incomparable R j hj w.val
  have hp : ∀ w, p (s w) ↔ p w := fun w =>
    not_congr (odd_incomparable_move R i j hi hj hij w)
  let q := fun w : {w // ¬p w} => w.val.val (leftPos j hj) < w.val.val (rightPos j hj)
  let a := s.subtypePerm (p := fun w => ¬p w) (fun w => not_congr (hp w))
  have hq : ∀ w, q (a w) ↔ q w := by
    intro w
    dsimp [q, a, s]
    rw [odd_move_outside R i hi _ _ (by dsimp [leftPos]; omega) (by dsimp [leftPos]; omega),
      odd_move_outside R i hi _ _ (by dsimp [rightPos]; omega) (by dsimp [rightPos]; omega)]
  have ht : ∀ w, p (t w) ↔ p w := fun w => not_congr (odd_incomparable_self R j hj w)
  let b := t.subtypePerm (p := fun w => ¬p w) (fun w => not_congr (ht w))
  have hbb : ∀ w, b (b w) = w := by
    intro w
    apply Subtype.ext
    exact move_involutive R j hj w.val
  have hbq : ∀ w, q (b w) ↔ ¬q w := by
    intro w
    have hc : incomparable R j hj w.val.val := not_not.mp w.property
    have hv := odd_move_pair R j hj w.val hc
    have hn : w.val.val (leftPos j hj) ≠ w.val.val (rightPos j hj) := by
      apply w.val.val.injective.ne
      intro h
      have := congrArg Fin.val h
      dsimp [leftPos, rightPos] at this
      omega
    change (t w.val).val (leftPos j hj) < (t w.val).val (rightPos j hj) ↔ _
    rw [hv.1, hv.2]
    exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans (or_iff_left hn)))
  let e : {w // q w} ≃ {w // ¬q w} :=
    { toFun := fun w => ⟨b w.val, fun h => ((hbq w.val).mp h) w.property⟩
      invFun := fun w => ⟨b w.val, (hbq w.val).mpr w.property⟩
      left_inv := fun w => Subtype.ext (hbb w.val)
      right_inv := fun w => Subtype.ext (hbb w.val) }
  apply odd_sign_cancel s p hp q hq e
  intro w
  apply Subtype.ext
  apply Subtype.ext
  exact (odd_move_commute R i j hi hj hij w.val.val).symm

#print axioms odd_sign_cancel_separated
end Zigzag
```

### `OddTail.lean`

```lean
import FenceEndpointFrames

set_option linter.unusedSimpArgs false

namespace Zigzag
open Equiv

/-- The remaining word, followed by the two vertices 0,1. -/
def oddTailPad {r : ℕ} (w : Perm (Fin r)) : Perm (Fin (r+2)) :=
  (splitCVertices r).trans ((optionCongr (optionCongr w)).trans (splitAVertices r).symm)

@[simp] theorem oddTailPad_zero {r : ℕ} (w : Perm (Fin r)) :
    oddTailPad w ⟨r, by omega⟩ = 0 := by
  rw [← splitC_first r]
  simp only [oddTailPad, trans_apply, apply_symm_apply, optionCongr_apply, Option.map_none]
  simp [splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem oddTailPad_one {r : ℕ} (w : Perm (Fin r)) :
    oddTailPad w (Fin.last (r+1)) = 1 := by
  rw [← splitC_last r]
  simp only [oddTailPad, trans_apply, apply_symm_apply, optionCongr_apply, Option.map_none, Option.map_some]
  simp [splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem oddTailPad_old {r : ℕ} (w : Perm (Fin r)) (a : Fin r) :
    oddTailPad w (a.castSucc.castSucc) = (w a).succ.succ := by
  have h : a.castSucc.castSucc = (splitCVertices r).symm (some (some a)) := by
    rw [splitC_middle]; rfl
  rw [h]
  simp only [oddTailPad, trans_apply, apply_symm_apply, optionCongr_apply, Option.map_some]
  simp [splitAVertices, ← Equiv.optionCongr_symm]

@[simp] theorem oddTailPad_symm_zero {r : ℕ} (w : Perm (Fin r)) :
    (oddTailPad w).symm 0 = ⟨r, by omega⟩ :=
  (oddTailPad w).symm_apply_eq.mpr (oddTailPad_zero w).symm
@[simp] theorem oddTailPad_symm_one {r : ℕ} (w : Perm (Fin r)) :
    (oddTailPad w).symm 1 = Fin.last (r+1) :=
  (oddTailPad w).symm_apply_eq.mpr (oddTailPad_one w).symm
@[simp] theorem oddTailPad_symm_old {r : ℕ} (w : Perm (Fin r)) (a : Fin r) :
    (oddTailPad w).symm a.succ.succ = (w.symm a).castSucc.castSucc := by
  apply (oddTailPad w).symm_apply_eq.mpr
  simp

/-- The tail construction preserves exactly the literal order condition. -/
theorem oddTailPad_isLE_iff {r : ℕ} (w : Perm (Fin r)) :
    IsLE (zigLt (r+2)) (oddTailPad w) ↔ IsLE (zigLt r) w := by
  constructor
  · intro h a b hab
    have hh := h a.succ.succ b.succ.succ ((zigLt_shift_two r a b).mpr hab)
    simpa only [oddTailPad_symm_old, Fin.castSucc_lt_castSucc_iff] using hh
  · intro h a b hab
    induction a using Fin.cases with
    | zero =>
      have hb : b = 1 := by
        apply Fin.ext
        simp only [Fin.val_one]
        have := hab.2
        simp only [Fin.val_zero] at this
        omega
      subst b
      simp [Fin.lt_def]
    | succ a =>
      induction a using Fin.cases with
      | zero => have := hab.1; change 1 % 2 = 0 at this; omega
      | succ a =>
        induction b using Fin.cases with
        | zero => have := hab.2; simp only [Fin.val_zero, Fin.val_succ] at this; omega
        | succ b =>
          induction b using Fin.cases with
          | zero =>
            simp only [oddTailPad_symm_old, oddTailPad_symm_one]
            exact lt_trans (show (w.symm a).castSucc.castSucc < (⟨r, by omega⟩ : Fin (r+2)) from
              (w.symm a).isLt) (by change r < r+1; omega)
          | succ b =>
            simpa only [oddTailPad_symm_old, Fin.castSucc_lt_castSucc_iff] using
              h a b ((zigLt_shift_two r a b).mp hab)

def oddTailExtension {r : ℕ} (w : ZigzagLE r) : ZigzagLE (r+2) :=
  ⟨oddTailPad w.val, (oddTailPad_isLE_iff w.val).mpr w.property⟩

def OddTailFiber (r : ℕ) := {w : ZigzagLE (r+2) //
  w.val ⟨r, by omega⟩ = 0 ∧ w.val (Fin.last (r+1)) = 1}

instance (r : ℕ) : Fintype (OddTailFiber r) := by unfold OddTailFiber; infer_instance
instance (r : ℕ) : DecidableEq (OddTailFiber r) := by unfold OddTailFiber; infer_instance

theorem oddTailPad_injective {r : ℕ} : Function.Injective (@oddTailPad r) := by
  intro w v h
  apply Equiv.ext
  intro a
  have hh := congrArg (fun e : Perm (Fin (r+2)) => e a.castSucc.castSucc) h
  simpa only [oddTailPad_old, Fin.succ_inj] using hh

/-- The fixed tail is the entire fiber, not only the image of padding. -/
theorem oddTail_exists_pad {r : ℕ} (w : OddTailFiber r) :
    ∃ v : ZigzagLE r, oddTailExtension v = w.val := by
  let e : Perm (Option (Option (Fin r))) :=
    (splitCVertices r).symm.trans (w.val.val.trans (splitAVertices r))
  have he0 : e none = none := by
    change splitAVertices r (w.val.val ((splitCVertices r).symm none)) = none
    rw [splitC_first, w.property.1]
    simp [splitAVertices]
  have he1 : e (some none) = some none := by
    change splitAVertices r (w.val.val ((splitCVertices r).symm (some none))) = some none
    rw [splitC_last, w.property.2]
    simp [splitAVertices]
  have hrec := EndpointFrame.optionCongr_removeNone_fixed e he0
  have hr0 : removeNone e none = none := by
    apply Option.some_injective
    have hh := Equiv.congr_fun hrec (some none)
    simpa only [optionCongr_apply, Option.map_none, Option.map_some, he1] using hh
  let v := removeNone (removeNone e)
  have hr : optionCongr (optionCongr v) = e := by
    rw [show optionCongr v = removeNone e from
      EndpointFrame.optionCongr_removeNone_fixed (removeNone e) hr0]
    exact hrec
  have hpad : oddTailPad v = w.val.val := by
    apply Equiv.ext
    intro a
    have hh := Equiv.congr_fun hr (splitCVertices r a)
    apply (splitAVertices r).injective
    simpa only [oddTailPad, Equiv.trans_apply, Equiv.apply_symm_apply,
      e, Equiv.symm_apply_apply] using hh
  have hv := (oddTailPad_isLE_iff v).mp (hpad ▸ w.val.property)
  exact ⟨⟨v, hv⟩, Subtype.ext hpad⟩

noncomputable def oddTailEquiv (r : ℕ) : ZigzagLE r ≃ OddTailFiber r :=
  Equiv.ofBijective (fun w => ⟨oddTailExtension w, oddTailPad_zero _, oddTailPad_one _⟩)
    ⟨fun _ _ h => Subtype.ext (oddTailPad_injective (congrArg (fun w => w.val.val) h)),
      fun w => by obtain ⟨v, hv⟩ := oddTail_exists_pad w; exact ⟨v, Subtype.ext hv⟩⟩

#print axioms oddTailPad_isLE_iff
#print axioms oddTail_exists_pad
#print axioms oddTailEquiv
end Zigzag
```

### `OddTailFixed.lean`

```lean
import OddTail

namespace Zigzag
open Equiv

/-- In an even fence, a comparable final pair is necessarily 0,1. -/
theorem odd_tail_comparable {r : ℕ} (hr : Even r) (w : ZigzagLE (r+2)) :
    ¬incomparable (zigLt (r+2)) r (by omega) w.val ↔
      w.val ⟨r, by omega⟩ = 0 ∧ w.val (Fin.last (r+1)) = 1 := by
  let a := w.val (⟨r, by omega⟩ : Fin (r+2))
  let b := w.val (Fin.last (r+1))
  have hposA : w.val.symm a = ⟨r, by omega⟩ := w.val.symm_apply_apply _
  have hposB : w.val.symm b = Fin.last (r+1) := w.val.symm_apply_apply _
  have hnmod : r % 2 = 0 := by obtain ⟨k, hk⟩ := hr; omega
  constructor
  · intro h
    have hab : zigLt (r+2) a b := by
      have hrev : ¬zigLt (r+2) b a := by
        intro hh
        have hh' := w.property b a hh
        rw [hposA, hposB] at hh'
        change r+1 < r at hh'
        omega
      change ¬(¬zigLt (r+2) a b ∧ ¬zigLt (r+2) b a) at h
      tauto
    have hamod := hab.1
    have ha0 : a.val = 0 := by
      by_contra hne
      have habound := a.isLt
      have haPlus : a.val+1 < r+2 := by omega
      let c : Fin (r+2) := ⟨a.val-1, by omega⟩
      let d : Fin (r+2) := ⟨a.val+1, haPlus⟩
      have hc : zigLt (r+2) a c := by dsimp [zigLt, c]; omega
      have hd : zigLt (r+2) a d := ⟨hamod, Or.inl rfl⟩
      have hpc := w.property a c hc
      have hpd := w.property a d hd
      rw [hposA] at hpc hpd
      have hbc := (w.val.symm c).isLt
      have hbd := (w.val.symm d).isLt
      have he : w.val.symm c = w.val.symm d := by
        apply Fin.ext
        change r < (w.val.symm c).val at hpc
        change r < (w.val.symm d).val at hpd
        omega
      have hh := congrArg Fin.val (w.val.symm.injective he)
      dsimp [c, d] at hh
      omega
    have hb1 : b.val = 1 := by have := hab.2; omega
    exact ⟨Fin.ext ha0, Fin.ext hb1⟩
  · rintro ⟨ha, hb⟩ h
    apply h.1
    change zigLt (r+2) (w.val ⟨r, by omega⟩) (w.val (Fin.last (r+1)))
    rw [ha, hb]
    exact ⟨rfl, Or.inl rfl⟩

/-- Tail padding intertwines each generator supported in the smaller word. -/
theorem oddTail_rawSwap {r : ℕ} (i : ℕ) (hi : i+1<r) (w : Perm (Fin r)) :
    rawSwap i (by omega : i+1<r+2) (oddTailPad w) =
      oddTailPad (rawSwap i hi w) := by
  apply Equiv.ext
  intro a
  induction a using Fin.lastCases with
  | last =>
    change oddTailPad w (adjacentSwap i _ (Fin.last (r+1))) =
      oddTailPad (rawSwap i hi w) (Fin.last (r+1))
    have hs : adjacentSwap i (by omega : i+1<r+2) (Fin.last (r+1)) = Fin.last (r+1) := by
      apply Equiv.swap_apply_of_ne_of_ne <;> intro he
      all_goals have hh := congrArg Fin.val he; dsimp [leftPos, rightPos] at hh; omega
    rw [hs, oddTailPad_one, oddTailPad_one]
  | cast a =>
    induction a using Fin.lastCases with
    | last =>
      change oddTailPad w (adjacentSwap i _ ⟨r, by omega⟩) =
        oddTailPad (rawSwap i hi w) ⟨r, by omega⟩
      have hs : adjacentSwap i (by omega : i+1<r+2) ⟨r, by omega⟩ = ⟨r, by omega⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne <;> intro he
        all_goals have hh := congrArg Fin.val he; dsimp [leftPos, rightPos] at hh; omega
      rw [hs, oddTailPad_zero, oddTailPad_zero]
    | cast a =>
      change oddTailPad w (adjacentSwap i _ a.castSucc.castSucc) = _
      have hs : adjacentSwap i (by omega : i+1<r+2) a.castSucc.castSucc =
          (adjacentSwap i hi a).castSucc.castSucc := by
        simp only [adjacentSwap, Equiv.swap_apply_def]
        split_ifs <;> simp_all [leftPos, rightPos, Fin.ext_iff]
      rw [hs, oddTailPad_old, oddTailPad_old]
      rfl

theorem oddTail_incomparable {r : ℕ} (i : ℕ) (hi : i+1<r) (w : Perm (Fin r)) :
    incomparable (zigLt (r+2)) i (by omega) (oddTailPad w) ↔
      incomparable (zigLt r) i hi w := by
  have hl : leftPos i (by omega : i+1<r+2) = (leftPos i hi).castSucc.castSucc := rfl
  have hr : rightPos i (by omega : i+1<r+2) = (rightPos i hi).castSucc.castSucc := rfl
  simp only [incomparable, hl, hr, oddTailPad_old]
  exact and_congr (not_congr (zigLt_shift_two r _ _)) (not_congr (zigLt_shift_two r _ _))

theorem oddTail_bk {r : ℕ} (i : ℕ) (hi : i+1<r) (w : ZigzagLE r) :
    bk (r+2) i (by omega) (oddTailExtension w) = oddTailExtension (bk r i hi w) := by
  apply Subtype.ext
  change (move (zigLt (r+2)) i _ (oddTailExtension w)).val = oddTailPad ((bk r i hi w).val)
  rw [move_apply]
  change (if incomparable (zigLt (r+2)) i _ (oddTailPad w.val) then _ else _) = _
  rw [show (bk r i hi w).val = _ from move_apply (zigLt r) i hi w]
  by_cases h : incomparable (zigLt r) i hi w.val
  · simp only [(oddTail_incomparable i hi w.val).mpr h, ite_true, h]
    exact oddTail_rawSwap i hi w.val
  · simp only [(oddTail_incomparable i hi w.val).not.mpr h, ite_false, h]
    rfl

#print axioms odd_tail_comparable
#print axioms oddTail_bk
end Zigzag
```

### `OddStepProof.lean`

```lean
import OddCancellation
import OddTailFixed
import ZigzagBases
import RemainingStatements

namespace Zigzag
open Equiv Equiv.Perm

/-- Removing the comparable final pair preserves the sign of the second BK
move. The other two tail-order pieces have equal signs and cancel. -/
theorem odd_sign_recurrence {r : ℕ} (hr : Even r) (h : 2<r) :
    sign (bk (r+2) 1 (by omega)) = sign (bk r 1 h) := by
  classical
  let p := fun w : ZigzagLE (r+2) => ¬incomparable (zigLt (r+2)) r (by omega) w.val
  have hp : ∀ w, p (bk (r+2) 1 (by omega) w) ↔ p w := fun w =>
    not_congr (odd_incomparable_move (zigLt (r+2)) 1 r (by omega) (by omega) h w)
  let e : ZigzagLE r ≃ {w // p w} :=
    (oddTailEquiv r).trans (Equiv.subtypeEquivRight (fun w => (odd_tail_comparable hr w).symm))
  have he : ∀ w, e (bk r 1 h w) = (bk (r+2) 1 (by omega)).subtypePerm hp (e w) := by
    intro w
    apply Subtype.ext
    exact (oddTail_bk 1 h w).symm
  exact (odd_sign_cancel_separated (zigLt (r+2)) 1 r (by omega) (by omega) h).trans
    (sign_eq_sign_of_equiv _ _ e he).symm

/-- The source t_2 is an odd permutation at every even order at least four. -/
theorem odd_sign_even (n : ℕ) (hn : Even n) (h4 : 4≤n) (h : 2<n) :
    sign (bk n 1 h) = -1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 4
    · subst n
      rw [middle_generator_four]
      exact sign_swap (by decide : leFour 3 ≠ leFour 4)
    · have hnmod : n % 2 = 0 := by obtain ⟨k, hk⟩ := hn; omega
      have h6 : 6≤n := by omega
      obtain ⟨r, rfl⟩ : ∃ r, n = r+2 := ⟨n-2, by omega⟩
      have hr : Even r := Nat.even_iff.mpr (by omega)
      exact (odd_sign_recurrence hr (by omega)).trans
        (ih r (by omega) hr (by omega) (by omega))

theorem oddStep_proved : OddStep := by
  intro n h hn h4
  exact odd_sign_even n hn h4 h

#print oddStep_proved
#print axioms odd_sign_recurrence
#print axioms odd_sign_even
#print axioms oddStep_proved
end Zigzag
```

### `FinalEndpoint.lean`

```lean
import PrimAlternatingStep
import OddStepProof
import ConditionalEndpoint

namespace Zigzag

theorem even_zigzag_LE_symmetric (n : ℕ) (hn : Even n) : BKgroup n = ⊤ :=
  even_zigzag_LE_symmetric_from_steps alternatingStep_proved oddStep_proved n hn

#print axioms even_zigzag_LE_symmetric
end Zigzag
```

### `FinalAudit.lean`

```lean
import FinalEndpoint

#print Zigzag.zigLt
#print Zigzag.IsLE
#print Zigzag.LinearExtensions
#print Zigzag.ZigzagLE
#print Zigzag.bk
#print Zigzag.BKgroup
#print Zigzag.leftPos
#print Zigzag.rightPos
#print Zigzag.adjacentSwap
#print Zigzag.rawSwap
#print Zigzag.incomparable
#print Zigzag.moveFun
#print Zigzag.move
#check Zigzag.zigLt_strictOrder
#check Zigzag.zigLt_comparable_iff
#check Zigzag.sourceLabelBridge
#check Zigzag.bk_source_labels
#check Zigzag.card_zigzagLE_four
#check Zigzag.card_zigzagLE_six
#print Zigzag.card_zigzagLE_four
#print Zigzag.card_zigzagLE_six

namespace Zigzag

theorem final_bk_literal (n i : ℕ) (hi : i + 1 < n) (w : ZigzagLE n) :
    (bk n i hi w).val =
      if ¬ zigLt n (w.val (leftPos i hi)) (w.val (rightPos i hi)) ∧
         ¬ zigLt n (w.val (rightPos i hi)) (w.val (leftPos i hi)) then
        (adjacentSwap i hi).trans w.val else w.val :=
  move_apply (zigLt n) i hi w

#check final_bk_literal
#check even_zigzag_LE_symmetric
#print axioms final_bk_literal
#print axioms even_zigzag_LE_symmetric
end Zigzag
```

### `StageThreeAudit.lean`

```lean
import ContinuationAudit
import FenceDiagonalIsolation
import FenceFiberClassification
import FenceCountSeparation

#eval Lean.versionString
#check Zigzag.EndpointFrame.pad_isLE_iff
#check Zigzag.EndpointFrame.exists_pad
#check Zigzag.EndpointFrame.fiberEquiv
#check Zigzag.EndpointFrame.bk_extension
#check Zigzag.endpointAEquiv
#check Zigzag.endpointBEquiv
#check Zigzag.endpointCEquiv
#check Zigzag.endpointA_range_iff
#check Zigzag.endpointB_range_iff
#check Zigzag.endpointC_range_iff
#check Zigzag.inConnectedFibers_iff_residualConnected
#check Zigzag.simultaneous_internal_lift
#check Zigzag.internal_action_exists
#check Zigzag.diagonal_image_full
#check Zigzag.internalProjection_range
#check Zigzag.internalProjection_surjective
#check Zigzag.internalProjection_action
#check Zigzag.badAction
#print Zigzag.BadImageSectionFree
#check Zigzag.diagonal_isolation_of_bad_sectionFree
#check Zigzag.card_double_le
#check Zigzag.vertices_lt_card
#check Zigzag.five_le_card
#check Zigzag.card_mono_succ
#check Zigzag.card_mono
#check Zigzag.card_strict_odd_succ
#check Zigzag.card_previous_lt
#check Zigzag.card_smaller_lt
#print Zigzag.AlternatingStep
#print Zigzag.OddStep
#check Zigzag.even_zigzag_LE_symmetric_from_steps
#print axioms Zigzag.EndpointFrame.fiberEquiv
#print axioms Zigzag.EndpointFrame.bk_extension
#print axioms Zigzag.endpointAEquiv
#print axioms Zigzag.endpointBEquiv
#print axioms Zigzag.endpointCEquiv
#print axioms Zigzag.inConnectedFibers_iff_residualConnected
#print axioms Zigzag.diagonal_image_full
#print axioms Zigzag.internalProjection_range
#print axioms Zigzag.diagonal_isolation_of_bad_sectionFree
#print axioms Zigzag.vertices_lt_card
#print axioms Zigzag.card_previous_lt
#print axioms Zigzag.card_smaller_lt
#print axioms Zigzag.even_zigzag_LE_symmetric_from_steps
```

### `StageFourAudit.lean`

```lean
import StageThreeAudit
import FenceBoundarySwitch

#eval Lean.versionString
#check Zigzag.ResidualFrame.pad_isLE_iff
#check Zigzag.ResidualFrame.exists_pad
#check Zigzag.ResidualFrame.fiberEquiv
#check Zigzag.ResidualFrame.bk_extension
#check Zigzag.ResidualFrame.restriction
#check Zigzag.ResidualFrame.restriction_surjective
#check Zigzag.ResidualFrame.ofWord_covers
#check Zigzag.sectionFree_range_of_ker_le
#check Zigzag.badResidualProduct_ker_le
#check Zigzag.badImageSectionFree_of_residuals
#check Zigzag.ResidualFrame.relation_piece
#check Zigzag.ResidualFrame.length_lt_of_disconnected
#check Zigzag.extensionRelEquiv
#check Zigzag.dualExtensionEquiv
#check Zigzag.ResidualFrame.componentEquiv
#check Zigzag.ResidualFrame.component_card
#check Zigzag.factorial_lt_alternating_card
#check Zigzag.residual_sectionFree_of_component_lt
#check Zigzag.ResidualFrame.sectionFree_of_disconnected
#check Zigzag.badImageSectionFree
#check Zigzag.diagonal_isolation
#check Zigzag.boundarySwitch_mem
#check Zigzag.boundarySwitch_apply
#check Zigzag.boundarySwitch_ends
#print Zigzag.AlternatingStep
#print Zigzag.OddStep
#check Zigzag.even_zigzag_LE_symmetric_from_steps
#print axioms Zigzag.ResidualFrame.fiberEquiv
#print axioms Zigzag.ResidualFrame.bk_extension
#print axioms Zigzag.ResidualFrame.restriction_surjective
#print axioms Zigzag.ResidualFrame.component_card
#print axioms Zigzag.ResidualFrame.sectionFree_of_disconnected
#print axioms Zigzag.badImageSectionFree
#print axioms Zigzag.diagonal_isolation
#print axioms Zigzag.boundarySwitch_apply
#print axioms Zigzag.boundarySwitch_ends
#print axioms Zigzag.even_zigzag_LE_symmetric_from_steps
```

### `StageFiveAudit.lean`

```lean
import StageFourAudit
import FenceFiberTransitivity

#eval Lean.versionString
#check Zigzag.boundarySwitch_A_connected
#check Zigzag.boundarySwitch_B_not_connected
#check Zigzag.boundarySwitch_C_connected
#check Zigzag.two_neutral_witnesses
#check Zigzag.right_witness_exists
#check Zigzag.right_left_correspondence
#check Zigzag.diagonal_singleton_intersection
#check Zigzag.isolated_threeCycle
#check Zigzag.threeCycle_mem
#check Zigzag.threeCycle_step
#check Zigzag.all_star_cycles
#check Zigzag.A_threeCycle_mem
#check Zigzag.Aonly_apply
#check Zigzag.Aonly_fixed
#check Zigzag.A_alternating_mem
#check Zigzag.block_A_saturated
#check Zigzag.block_internal_invariant
#check Zigzag.relationBK_transitive
#check Zigzag.internal_fiber_transitive
#check Zigzag.block_absorbs_fiber
#check Zigzag.BKgroup_transitive
#print Zigzag.AlternatingStep
#print Zigzag.OddStep
#check Zigzag.even_zigzag_LE_symmetric_from_steps
#print axioms Zigzag.boundarySwitch_A_connected
#print axioms Zigzag.boundarySwitch_B_not_connected
#print axioms Zigzag.boundarySwitch_C_connected
#print axioms Zigzag.two_neutral_witnesses
#print axioms Zigzag.right_witness_exists
#print axioms Zigzag.right_left_correspondence
#print axioms Zigzag.diagonal_singleton_intersection
#print axioms Zigzag.isolated_threeCycle
#print axioms Zigzag.threeCycle_mem
#print axioms Zigzag.threeCycle_step
#print axioms Zigzag.all_star_cycles
#print axioms Zigzag.A_threeCycle_mem
#print axioms Zigzag.Aonly_apply
#print axioms Zigzag.Aonly_fixed
#print axioms Zigzag.A_alternating_mem
#print axioms Zigzag.block_A_saturated
#print axioms Zigzag.block_internal_invariant
#print axioms Zigzag.relationBK_transitive
#print axioms Zigzag.internal_fiber_transitive
#print axioms Zigzag.block_absorbs_fiber
#print axioms Zigzag.BKgroup_transitive
#print axioms Zigzag.even_zigzag_LE_symmetric_from_steps
```


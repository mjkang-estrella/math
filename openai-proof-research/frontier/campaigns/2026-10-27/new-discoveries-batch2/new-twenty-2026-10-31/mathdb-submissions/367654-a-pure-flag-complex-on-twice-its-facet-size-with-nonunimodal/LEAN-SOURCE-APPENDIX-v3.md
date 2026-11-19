# COMPLETE LEAN SOURCE APPENDIX v3

All imported local production sources, in topological order. UTF-8 payloads include their final newline. Failed drafts are excluded. Upstream specific Mathlib imports use PINS.json.

<!-- BEGIN LEAN MODULE Complex SHA256 736d185ef95a2954163dac1e9b7d1888322d1cc49d289f2609c6cfeb262de504 -->
```lean
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

namespace PureFlag
variable {V : Type*}
-- Faces are actual finite subsets, including all actual vertices.
def Independent (R : V → V → Prop) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ R u v

theorem independent_downward (R : V → V → Prop) {s t : Finset V}
    (h : Independent R s) (ht : t ⊆ s) : Independent R t := by
  intro u hu v hv
  exact h u (ht hu) v (ht hv)

theorem independent_empty (R : V → V → Prop) : Independent R ∅ := by
  simp [Independent]

theorem independent_singleton [DecidableEq V] (R : V → V → Prop)
    (hR : ∀ v, ¬ R v v) (v : V) : Independent R {v} := by
  simpa [Independent] using hR v

theorem independent_flag [DecidableEq V] (R : V → V → Prop)
    (hR : ∀ v, ¬ R v v) (s : Finset V)
    (hp : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Independent R {u,v}) :
    Independent R s := by
  intro u hu v hv
  by_cases h : u = v
  · subst v; exact hR u
  · exact hp u hu v hv h u (by simp) v (by simp)

abbrev Branch (a p q : ℕ) := (Fin a × Fin p) ⊕ (Fin a × Fin q)
def key {a p q : ℕ} : Branch a p q → (Fin a ⊕ Fin a)
  | .inl v => .inl v.1
  | .inr v => .inr v.1

def BranchAdj {a p q : ℕ} (u v : Branch a p q) : Prop :=
  u ≠ v ∧ key u = key v

abbrev Vertices (a : ℕ) := (Branch a 1 5 ⊕ Branch a 2 3) ⊕ Fin (7*a)

def Adj {a : ℕ} : Vertices a → Vertices a → Prop
  | .inl (.inl u), .inl (.inl v) => BranchAdj u v
  | .inl (.inr u), .inl (.inr v) => BranchAdj u v
  | .inl (.inl _), .inl (.inr _) => True
  | .inl (.inr _), .inl (.inl _) => True
  | _, _ => False

theorem adj_irreflexive {a : ℕ} (v : Vertices a) : ¬ Adj v v := by
  rcases v with (u | v) | e
  · simp [Adj, BranchAdj]
  · simp [Adj, BranchAdj]
  · simp [Adj]

theorem adj_symmetric {a : ℕ} (u v : Vertices a) : Adj u v ↔ Adj v u := by
  rcases u with (u | u) | u <;> rcases v with (v | v) | v <;>
    simp [Adj, BranchAdj, eq_comm]


theorem vertices_card (a : ℕ) : Fintype.card (Vertices a) = 18*a := by
  simp only [Vertices, Branch, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem actual_vertex (a : ℕ) (v : Vertices a) : Independent Adj {v} := by
  classical
  exact independent_singleton Adj adj_irreflexive v

#print axioms independent_flag
#print axioms adj_symmetric
#print axioms vertices_card
#print axioms actual_vertex
#eval Lean.versionString
end PureFlag
```
<!-- END LEAN MODULE Complex -->

<!-- BEGIN LEAN MODULE Join SHA256 88650a7230c160b8361e64e6bc4a2a64f539cdb12788f88079753193e7c48265 -->
```lean
import Complex
import Mathlib.Data.Finset.Sum

namespace PureFlag
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

def JoinRel (R : A → A → Prop) (S : B → B → Prop) : (A ⊕ B) → (A ⊕ B) → Prop
  | .inl u, .inl v => R u v
  | .inr u, .inr v => S u v
  | _, _ => True

def DisjointRel (R : A → A → Prop) (S : B → B → Prop) : (A ⊕ B) → (A ⊕ B) → Prop
  | .inl u, .inl v => R u v
  | .inr u, .inr v => S u v
  | _, _ => False

theorem join_faces (R : A → A → Prop) (S : B → B → Prop)
    (s : Finset A) (t : Finset B) :
    Independent (JoinRel R S) (s.disjSum t) ↔
      Independent R s ∧ Independent S t ∧ (s = ∅ ∨ t = ∅) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      exact h (.inl u) (by simp [hu]) (.inl v) (by simp [hv])
    · intro u hu v hv
      exact h (.inr u) (by simp [hu]) (.inr v) (by simp [hv])
    · by_cases hs : s = ∅
      · exact Or.inl hs
      · right
        by_contra ht
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr ht
        exact h (.inl u) (by simp [hu]) (.inr v) (by simp [hv]) trivial
  · rintro ⟨hs, ht, hempty⟩ u hu v hv
    rcases u with u | u <;> rcases v with v | v
    · exact hs u (by simpa using hu) v (by simpa using hv)
    · rcases hempty with he | he
      · simp [he] at hu
      · simp [he] at hv
    · rcases hempty with he | he
      · simp [he] at hv
      · simp [he] at hu
    · exact ht u (by simpa using hu) v (by simpa using hv)

omit [DecidableEq A] [DecidableEq B] in
theorem disjoint_faces (R : A → A → Prop) (S : B → B → Prop)
    (s : Finset A) (t : Finset B) :
    Independent (DisjointRel R S) (s.disjSum t) ↔
      Independent R s ∧ Independent S t := by
  constructor
  · intro h
    constructor
    · intro u hu v hv
      exact h (.inl u) (by simp [hu]) (.inl v) (by simp [hv])
    · intro u hu v hv
      exact h (.inr u) (by simp [hu]) (.inr v) (by simp [hv])
  · rintro ⟨hs, ht⟩ u hu v hv
    rcases u with u | u <;> rcases v with v | v
    · exact hs u (by simpa using hu) v (by simpa using hv)
    · exact not_false
    · exact not_false
    · exact ht u (by simpa using hu) v (by simpa using hv)

-- The two branch embeddings overlap at exactly the empty face.
omit [DecidableEq A] [DecidableEq B] in
theorem empty_overlap (s : Finset A) (t : Finset B)
    (h : s.disjSum (∅ : Finset B) = (∅ : Finset A).disjSum t) :
    s = ∅ ∧ t = ∅ := by
  have hl := congrArg Finset.toLeft h
  have hr := congrArg Finset.toRight h
  simpa only [Finset.toLeft_disjSum, Finset.toRight_disjSum] using And.intro hl hr.symm

omit [DecidableEq A] [DecidableEq B] in
theorem split_card (s : Finset (A ⊕ B)) :
    s.card = s.toLeft.card + s.toRight.card := by
  exact Finset.card_toLeft_add_card_toRight.symm

#print axioms join_faces
#print axioms disjoint_faces
#print axioms empty_overlap
#print axioms split_card
end PureFlag
```
<!-- END LEAN MODULE Join -->

<!-- BEGIN LEAN MODULE FaceBijections SHA256 5dbb2b89a7d4b7fac2b4c33c60dce85b83f45b9b9b70173fe09d596d0ebaf33c -->
```lean
import Join
import Mathlib.Data.Fintype.Powerset
namespace PureFlag
abbrev Faces {V : Type*} (R : V → V → Prop) := {s : Finset V // Independent R s}
noncomputable instance facesFintype {V : Type*} [Fintype V] (R : V → V → Prop) : Fintype (Faces R) := by
  classical
  exact Fintype.ofFinite _
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
noncomputable def disjointFaceEquiv (R : A → A → Prop) (S : B → B → Prop) :
    Faces (DisjointRel R S) ≃ Faces R × Faces S where
  toFun u := ⟨⟨u.val.toLeft, ((disjoint_faces R S _ _).mp (by rw [Finset.toLeft_disjSum_toRight]; exact u.property)).1⟩,
    ⟨u.val.toRight, ((disjoint_faces R S _ _).mp (by rw [Finset.toLeft_disjSum_toRight]; exact u.property)).2⟩⟩
  invFun p := ⟨p.1.val.disjSum p.2.val,(disjoint_faces R S _ _).mpr ⟨p.1.property,p.2.property⟩⟩
  left_inv u := Subtype.ext Finset.toLeft_disjSum_toRight
  right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> simp only [Finset.toLeft_disjSum,Finset.toRight_disjSum]

omit [DecidableEq A] [DecidableEq B] in
theorem disjointFaceEquiv_size (R : A → A → Prop) (S : B → B → Prop)
    (u : Faces (DisjointRel R S)) :
    u.val.card = ((disjointFaceEquiv R S u).1.val.card + (disjointFaceEquiv R S u).2.val.card) :=
  split_card _

noncomputable def joinEncode (R : A → A → Prop) (S : B → B → Prop) :
    Faces R ⊕ {s : Faces S // s.val.Nonempty} → Faces (JoinRel R S)
  | .inl s => ⟨s.val.disjSum ∅,(join_faces R S _ _).mpr ⟨s.property,independent_empty S,Or.inr rfl⟩⟩
  | .inr t => ⟨(∅ : Finset A).disjSum t.val.val,(join_faces R S _ _).mpr ⟨independent_empty R,t.val.property,Or.inl rfl⟩⟩

noncomputable def joinFaceEquiv (R : A → A → Prop) (S : B → B → Prop) :
    (Faces R ⊕ {s : Faces S // s.val.Nonempty}) ≃ Faces (JoinRel R S) :=
  Equiv.ofBijective (joinEncode R S) (by
    constructor
    · intro u v he
      have hh := congrArg Subtype.val he
      cases u with
      | inl s =>
        cases v with
        | inl t =>
          apply congrArg Sum.inl; apply Subtype.ext
          simpa only [joinEncode,Finset.toLeft_disjSum] using congrArg Finset.toLeft hh
        | inr t =>
          have he' : (∅ : Finset B) = t.val.val := by
            simpa only [joinEncode,Finset.toRight_disjSum] using congrArg Finset.toRight hh
          exact (t.property.ne_empty he'.symm).elim
      | inr s =>
        cases v with
        | inl t =>
          have he' : s.val.val = (∅ : Finset B) := by
            simpa only [joinEncode,Finset.toRight_disjSum] using congrArg Finset.toRight hh
          exact (s.property.ne_empty he').elim
        | inr t =>
          apply congrArg Sum.inr; apply Subtype.ext; apply Subtype.ext
          simpa only [joinEncode,Finset.toRight_disjSum] using congrArg Finset.toRight hh
    · intro u
      have hf := (join_faces R S u.val.toLeft u.val.toRight).mp
        (by rw [Finset.toLeft_disjSum_toRight]; exact u.property)
      by_cases hr : u.val.toRight = ∅
      · refine ⟨.inl ⟨u.val.toLeft,hf.1⟩,Subtype.ext ?_⟩
        change u.val.toLeft.disjSum ∅ = u.val
        rw [← hr,Finset.toLeft_disjSum_toRight]
      · have hl : u.val.toLeft = ∅ := hf.2.2.resolve_right hr
        refine ⟨.inr ⟨⟨u.val.toRight,hf.2.1⟩,Finset.nonempty_iff_ne_empty.mpr hr⟩,Subtype.ext ?_⟩
        change (∅ : Finset A).disjSum u.val.toRight = u.val
        rw [← hl,Finset.toLeft_disjSum_toRight])

theorem joinEncode_size (R : A → A → Prop) (S : B → B → Prop)
    (u : Faces R ⊕ {s : Faces S // s.val.Nonempty}) :
    (joinFaceEquiv R S u).val.card = Sum.elim (fun s : Faces R => s.val.card)
      (fun s : {s : Faces S // s.val.Nonempty} => s.val.val.card) u := by
  cases u <;> simp [joinFaceEquiv,joinEncode,Equiv.ofBijective]
#print axioms disjointFaceEquiv
#print axioms disjointFaceEquiv_size
#print axioms joinFaceEquiv
#print axioms joinEncode_size
end PureFlag
```
<!-- END LEAN MODULE FaceBijections -->

<!-- BEGIN LEAN MODULE FacePolynomial SHA256 7b2567f96f5478329872902f25579b73ea306798ce425748b491f4f7c44070dd -->
```lean
import FaceBijections
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
namespace PureFlag
open scoped BigOperators
open Polynomial
noncomputable def facePoly {V : Type*} [Fintype V] (R : V → V → Prop) : ℤ[X] :=
  ∑ s : Faces R, X ^ s.val.card

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [DecidableEq A] [DecidableEq B] in
theorem facePoly_disjoint (R : A → A → Prop) (S : B → B → Prop) :
    facePoly (DisjointRel R S) = facePoly R * facePoly S := by
  classical
  unfold facePoly
  rw [Fintype.sum_equiv (disjointFaceEquiv R S) _
    (fun p : Faces R × Faces S => X ^ (p.1.val.card + p.2.val.card))
    (fun u => congrArg (fun n => (X : ℤ[X])^n) (disjointFaceEquiv_size R S u))]
  simp only [Fintype.sum_prod_type,pow_add,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
theorem nonempty_face_sum (S : B → B → Prop) :
    (∑ s : {s : Faces S // s.val.Nonempty}, (X : ℤ[X])^s.val.val.card) + 1 = facePoly S := by
  classical
  have he : (∑ s : {s : Faces S // ¬s.val.Nonempty}, (X : ℤ[X])^s.val.val.card) = 1 := by
    let e : {s : Faces S // ¬s.val.Nonempty} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨⟨∅,independent_empty S⟩,by simp⟩
        left_inv := by intro s; apply Subtype.ext; apply Subtype.ext; exact (Finset.not_nonempty_iff_eq_empty.mp s.property).symm
        right_inv := by intro u; cases u; rfl }
    rw [Fintype.sum_equiv e _ (fun _ => (1 : ℤ[X])) (by
      intro s
      rw [Finset.not_nonempty_iff_eq_empty.mp s.property]
      simp)]
    simp
  rw [← he]
  exact Fintype.sum_subtype_add_sum_subtype (fun s : Faces S => s.val.Nonempty) (fun s => (X : ℤ[X])^s.val.card)

theorem facePoly_join (R : A → A → Prop) (S : B → B → Prop) :
    facePoly (JoinRel R S) = facePoly R + facePoly S - 1 := by
  classical
  have h := Fintype.sum_equiv (joinFaceEquiv R S)
    (fun u => Sum.elim (fun s : Faces R => (X : ℤ[X])^s.val.card)
      (fun s : {s : Faces S // s.val.Nonempty} => X^s.val.val.card) u)
    (fun u => (X : ℤ[X])^u.val.card)
    (by intro u; rw [joinEncode_size]; cases u <;> rfl)
  rw [Fintype.sum_sum_type] at h
  simp only [Sum.elim_inl,Sum.elim_inr] at h
  have he := nonempty_face_sum S
  unfold facePoly at *
  rw [← h, ← he]
  ring

omit [DecidableEq A] in
theorem facePoly_coeff_count (R : A → A → Prop) (n : ℕ) :
    (facePoly R).coeff n = (Fintype.card {s : Faces R // s.val.card = n} : ℤ) := by
  classical
  simp [facePoly,Polynomial.coeff_X_pow,eq_comm,Fintype.card_subtype]

#print axioms facePoly
#print axioms facePoly_disjoint
#print axioms nonempty_face_sum
#print axioms facePoly_join
#print axioms facePoly_coeff_count
end PureFlag
```
<!-- END LEAN MODULE FacePolynomial -->

<!-- BEGIN LEAN MODULE Choices SHA256 8cd389de6e7cc52d8b1c509d3cd200f26a723aaf2066ca52a909882c4df42502 -->
```lean
import Complex
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

namespace PureFlag
variable {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

def Partial (s : Finset (I × T)) : Prop :=
  ∀ i x y, (i,x) ∈ s → (i,y) ∈ s → x = y

def encode (f : I → Option T) : Finset (I × T) :=
  Finset.univ.filter (fun p => f p.1 = some p.2)

omit [DecidableEq I] in
@[simp] theorem mem_encode (f : I → Option T) (i : I) (t : T) :
    (i,t) ∈ encode f ↔ f i = some t := by simp [encode]

omit [DecidableEq I] in
theorem encode_partial (f : I → Option T) : Partial (encode f) := by
  intro i x y hx hy
  simp only [mem_encode] at hx hy
  exact Option.some.inj (hx.symm.trans hy)

omit [DecidableEq I] in
theorem encode_injective : Function.Injective (encode (I:=I) (T:=T)) := by
  intro f g h
  funext i
  have hm : ∀ t, f i = some t ↔ g i = some t := by
    intro t
    simpa only [mem_encode] using (show (i,t) ∈ encode f ↔ (i,t) ∈ encode g by rw [h])
  cases hf : f i with
  | none =>
    cases hg : g i with
    | none => rfl
    | some t => have := (hm t).mpr hg; simp [hf] at this
  | some t => exact ((hm t).mp hf).symm

noncomputable def decode (s : Finset (I × T)) (i : I) : Option T :=
  if h : ∃ t, (i,t) ∈ s then some (Classical.choose h) else none

omit [Fintype I] in
theorem decode_spec (s : Finset (I × T)) (hs : Partial s) (i : I) (t : T) :
    decode s i = some t ↔ (i,t) ∈ s := by
  classical
  unfold decode
  split_ifs with h
  · constructor
    · intro he
      have he' := Option.some.inj he
      rw [← he']
      exact Classical.choose_spec h
    · intro ht
      congr 1
      exact hs i _ t (Classical.choose_spec h) ht
  · constructor
    · intro he; cases he
    · intro ht; exact (h ⟨t,ht⟩).elim

theorem encode_decode (s : Finset (I × T)) (hs : Partial s) :
    encode (decode s) = s := by
  ext p
  exact (mem_encode _ p.1 p.2).trans (decode_spec s hs p.1 p.2)

noncomputable def choiceEquiv : (I → Option T) ≃ {s : Finset (I × T) // Partial s} :=
  Equiv.ofBijective (fun f => ⟨encode f, encode_partial f⟩) (by
    constructor
    · intro f g h
      exact encode_injective (congrArg Subtype.val h)
    · intro s
      exact ⟨decode s.val, Subtype.ext (encode_decode s.val s.property)⟩)

omit [Fintype I] [Fintype T] [DecidableEq I] in
theorem partial_iff_independent (s : Finset (I × T)) :
    Partial s ↔ Independent (fun u v : I × T => u ≠ v ∧ u.1 = v.1) s := by
  constructor
  · intro hs u hu v hv ⟨hne, heq⟩
    apply hne
    apply Prod.ext heq
    apply hs u.1 u.2 v.2 hu
    simpa only [heq] using hv
  · intro hs i x y hx hy
    by_contra hne
    exact hs (i,x) hx (i,y) hy ⟨by intro h; exact hne (congrArg Prod.snd h), rfl⟩

#print axioms choiceEquiv
#print axioms encode_decode
#print axioms partial_iff_independent
end PureFlag
```
<!-- END LEAN MODULE Choices -->

<!-- BEGIN LEAN MODULE ChoiceCounts SHA256 0d1e501870c21979dd1b77e88404dcfd4e4956f4c08ad6d73ce561a105ca405e -->
```lean
import Choices
import Mathlib.Data.Fintype.BigOperators

namespace PureFlag
variable {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

omit [DecidableEq I] in
theorem encode_card (f : I → Option T) :
    (encode f).card = (Finset.univ.filter (fun i => f i ≠ none)).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    have he := (mem_encode f p.1 p.2).mp hp
    simp [he]
  · intro p hp q hq he
    have h₁ := (mem_encode f p.1 p.2).mp hp
    have h₂ := (mem_encode f q.1 q.2).mp hq
    apply Prod.ext he
    rw [← he] at h₂
    exact Option.some.inj (h₁.symm.trans h₂)
  · intro i hi
    have hn : f i ≠ none := (Finset.mem_filter.mp hi).2
    cases he : f i with
    | none => exact (hn he).elim
    | some t => exact ⟨(i,t), (mem_encode f i t).mpr he, rfl⟩

omit [DecidableEq I] in
theorem encode_none : encode (fun _ : I => (none : Option T)) = ∅ := by
  ext p
  simp [encode]

noncomputable instance partialFintype : Fintype {s : Finset (I × T) // Partial s} :=
  Fintype.ofEquiv (I → Option T) choiceEquiv

theorem partial_count : Fintype.card {s : Finset (I × T) // Partial s} =
    (Fintype.card T + 1) ^ Fintype.card I := by
  rw [← Fintype.card_congr (choiceEquiv (I:=I) (T:=T))]
  simp [Fintype.card_option]

-- Maximality is inclusion maximality of the genuine finite subsets.
def MaxPartial (s : Finset (I × T)) : Prop :=
  Partial s ∧ ∀ t, Partial t → s ⊆ t → t = s

omit [Fintype I] in
theorem maxPartial_full [Nonempty T] (s : Finset (I × T)) (hs : MaxPartial s) :
    ∀ i, ∃ t, (i,t) ∈ s := by
  classical
  intro i
  by_contra hn
  have hnone : ∀ t, (i,t) ∉ s := by simpa using hn
  let x : T := Classical.choice inferInstance
  have hp : Partial (insert (i,x) s) := by
    intro j u v hu hv
    simp only [Finset.mem_insert] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (congrArg Prod.snd hu).trans (congrArg Prod.snd hv).symm
    · have hj : j = i := congrArg Prod.fst hu
      exact (hnone v (by simpa only [hj] using hv)).elim
    · have hj : j = i := congrArg Prod.fst hv
      exact (hnone u (by simpa only [hj] using hu)).elim
    · exact hs.1 j u v hu hv
  have he := hs.2 (insert (i,x) s) hp (Finset.subset_insert _ _)
  have hm : (i,x) ∈ s := by rw [← he]; simp
  exact hnone x hm

theorem maxPartial_card [Nonempty T] (s : Finset (I × T)) (hs : MaxPartial s) :
    s.card = Fintype.card I := by
  have he := encode_decode s hs.1
  rw [← he, encode_card]
  have hf : ∀ i, decode s i ≠ none := by
    intro i
    obtain ⟨t, ht⟩ := maxPartial_full s hs i
    rw [(decode_spec s hs.1 i t).mpr ht]
    simp
  simp [hf]

#print axioms encode_card
#print axioms partial_count
#print axioms maxPartial_card


end PureFlag
```
<!-- END LEAN MODULE ChoiceCounts -->

<!-- BEGIN LEAN MODULE Purity SHA256 9661e08599af0b4cd4c2548fabc6cdaa9f8ba438d1f0f2bb31978938ffcb4745 -->
```lean
import Join
import Mathlib.Data.Fintype.BigOperators
namespace PureFlag
variable {V K A B : Type*}
def MaxInd (R : V → V → Prop) (s : Finset V) : Prop :=
  Independent R s ∧ ∀ t, Independent R t → s ⊆ t → t = s

theorem keyed_card [Fintype K] [DecidableEq V] (k : V → K)
    (rep : K → V) (hr : ∀ i, k (rep i) = i) (s : Finset V)
    (hs : MaxInd (fun u v => u ≠ v ∧ k u = k v) s) : s.card = Fintype.card K := by
  classical
  apply Finset.card_bij (fun v _ => k v)
  · intro v hv; simp
  · intro u hu v hv he
    by_contra hn
    exact hs.1 u hu v hv ⟨hn,he⟩
  · intro i hi
    by_contra hn
    have hn' : ∀ v ∈ s, k v ≠ i := by simpa using hn
    have hp : Independent (fun u v => u ≠ v ∧ k u = k v) (insert (rep i) s) := by
      intro u hu v hv ⟨hne,he⟩
      simp only [Finset.mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact hne rfl
      · exact hn' v hv (he.symm.trans (hr i))
      · exact hn' u hu (he.trans (hr i))
      · exact hs.1 u hu v hv ⟨hne,he⟩
    have he := hs.2 _ hp (Finset.subset_insert _ _)
    have hm : rep i ∈ s := by rw [← he]; simp
    exact hn' _ hm (hr i)

variable [DecidableEq A] [DecidableEq B]
omit [DecidableEq A] [DecidableEq B] in
theorem max_disjoint (R : A → A → Prop) (S : B → B → Prop)
    (s : Finset A) (t : Finset B) :
    MaxInd (DisjointRel R S) (s.disjSum t) ↔ MaxInd R s ∧ MaxInd S t := by
  constructor
  · intro h
    have hf := (disjoint_faces R S s t).mp h.1
    constructor
    · refine ⟨hf.1, ?_⟩
      intro u hu hsu
      have he := h.2 (u.disjSum t) ((disjoint_faces R S u t).mpr ⟨hu,hf.2⟩)
        (Finset.disjSum_subset.mpr (by simpa using And.intro hsu (Finset.Subset.refl t)))
      simpa using congrArg Finset.toLeft he
    · refine ⟨hf.2, ?_⟩
      intro u hu htu
      have he := h.2 (s.disjSum u) ((disjoint_faces R S s u).mpr ⟨hf.1,hu⟩)
        (Finset.disjSum_subset.mpr (by simpa using And.intro (Finset.Subset.refl s) htu))
      simpa using congrArg Finset.toRight he
  · rintro ⟨hs,ht⟩
    refine ⟨(disjoint_faces R S s t).mpr ⟨hs.1,ht.1⟩, ?_⟩
    intro u hu hsu
    have hf := (disjoint_faces R S u.toLeft u.toRight).mp (by rw [Finset.toLeft_disjSum_toRight]; exact hu)
    have hsub := Finset.disjSum_subset.mp hsu
    have hl := hs.2 _ hf.1 hsub.1
    have hr := ht.2 _ hf.2 hsub.2
    rw [← (Finset.toLeft_disjSum_toRight (u := u)), hl, hr]

theorem max_join_left (R : A → A → Prop) (S : B → B → Prop)
    (s : Finset A) (hn : s.Nonempty) (hs : MaxInd R s) :
    MaxInd (JoinRel R S) (s.disjSum ∅) := by
  refine ⟨(join_faces R S s ∅).mpr ⟨hs.1, independent_empty S, Or.inr rfl⟩, ?_⟩
  intro u hu hsu
  have hf := (join_faces R S u.toLeft u.toRight).mp (by rw [Finset.toLeft_disjSum_toRight]; exact hu)
  have hsub := (Finset.disjSum_subset.mp hsu).1
  have hl := hs.2 _ hf.1 hsub
  have hr : u.toRight = ∅ := by
    rcases hf.2.2 with he | he
    · have : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro v hv; have := hsub hv; simp [he] at this)
      exact (hn.ne_empty this).elim
    · exact he
  rw [← (Finset.toLeft_disjSum_toRight (u := u)), hl, hr]

#print axioms keyed_card
#print axioms max_disjoint
#print axioms max_join_left
end PureFlag
```
<!-- END LEAN MODULE Purity -->

<!-- BEGIN LEAN MODULE Valley SHA256 3b4c961ede3c228484b482e09862cc03f289cbc7f7880ce24a26de90f32c2297 -->
```lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum

namespace PureFlag
-- A global mode predicate; finite-list/zero-extension transport remains separate.
def HasMode (u : ℤ → ℚ) : Prop :=
  ∃ m : ℤ, (∀ i j, i ≤ j → j ≤ m → u i ≤ u j) ∧
    (∀ i j, m ≤ i → i ≤ j → u j ≤ u i)

theorem no_reversed_window_signs (u : ℤ → ℚ) (hu : HasMode u)
    (s t L : ℤ) (hst : s < t) (hL : 0 ≤ L)
    (hs : u (s + L) < u s) (ht : u t < u (t + L)) : False := by
  obtain ⟨m, inc, dec⟩ := hu
  have hm1 : m < s + L := by
    by_contra h
    have hle : s + L ≤ m := le_of_not_gt h
    have := inc s (s + L) (by omega) hle
    linarith
  have hm2 : t < m := by
    by_contra h
    have hle : m ≤ t := le_of_not_gt h
    have := dec t (t + L) hle (by omega)
    linarith
  have hleft := inc s t (le_of_lt hst) (le_of_lt hm2)
  have hright := dec (s + L) (t + L) (le_of_lt hm1) (by omega)
  linarith

theorem point_valley_not_mode (u : ℤ → ℚ) (i j k : ℤ)
    (hij : i ≤ j) (hjk : j ≤ k) (hl : u j < u i) (hr : u j < u k) :
    ¬ HasMode u := by
  rintro ⟨m, inc, dec⟩
  by_cases h : j ≤ m
  · have := inc i j hij h
    linarith
  · have := dec j k (by omega) hjk
    linarith

theorem rational_block_valley (q b₁ b₂ b₃ : ℚ)
    (hq : q ≤ 1 / 12)
    (h₁ : 1 - 308 / 1875 - q ≤ b₁)
    (h₃ : 1 - 311 / 1875 - q ≤ b₃)
    (h₂ : b₂ ≤ (2 - q) - b₁ - b₃) :
    b₂ < b₁ ∧ b₂ < b₃ := by
  constructor <;> linarith

theorem exact_leaf_values :
    (192500 / 3 : ℚ) / 625^2 = 308 / 1875 ∧
    (194375 / 3 : ℚ) / 625^2 = 311 / 1875 ∧
    (1 - 308 / 1875 - 2 / 3 - (2 / 3) * (1 / 12) : ℚ) = 1277 / 11250 ∧
    (1 - 311 / 1875 - 2 / 3 - (2 / 3) * (1 / 12) : ℚ) = 1259 / 11250 := by
  norm_num

#print axioms no_reversed_window_signs
#print axioms point_valley_not_mode
#print axioms rational_block_valley
#print axioms exact_leaf_values
end PureFlag
```
<!-- END LEAN MODULE Valley -->

<!-- BEGIN LEAN MODULE Endpoint SHA256 6898443a3bdb75703eadb179989f52c9fead6c316e262fa899958f65b452d957 -->
```lean
import Complex
import Valley
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum

namespace PureFlag
variable (V : Type*) [Fintype V] [DecidableEq V]

structure FiniteComplex where
  face : Finset V → Prop
  empty_face : face ∅
  singleton_face : ∀ v, face {v}
  downward : ∀ {s t}, face s → t ⊆ s → face t

namespace FiniteComplex
variable {V}
def Facet (K : FiniteComplex V) (s : Finset V) : Prop :=
  K.face s ∧ ∀ t, K.face t → s ⊆ t → t = s

def Pure (K : FiniteComplex V) (d : ℕ) : Prop :=
  (∃ s, K.Facet s) ∧ ∀ s, K.Facet s → s.card = d

def Flag (K : FiniteComplex V) : Prop :=
  ∀ s, (∀ u ∈ s, ∀ v ∈ s, u ≠ v → K.face {u,v}) → K.face s

noncomputable def f (K : FiniteComplex V) (i : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset V).powerset.filter
    (fun s => K.face s ∧ s.card = i+1)).card

def Unimodal (K : FiniteComplex V) (d : ℕ) : Prop :=
  ∃ m : ℕ, m < d ∧
    (∀ i j, i ≤ j → j ≤ m → K.f i ≤ K.f j) ∧
    (∀ i j, m ≤ i → i ≤ j → j < d → K.f j ≤ K.f i)
end FiniteComplex

noncomputable instance verticesDecidableEq (a : ℕ) : DecidableEq (Vertices a) := Classical.decEq _

noncomputable def graphComplex (a : ℕ) : FiniteComplex (Vertices a) := by
  classical
  exact ⟨Independent Adj, independent_empty Adj,
    independent_singleton Adj adj_irreflexive,
    fun h ht => independent_downward Adj h ht⟩

theorem graphComplex_flag (a : ℕ) : (graphComplex a).Flag := by
  classical
  exact independent_flag Adj adj_irreflexive

theorem witness_vertices : Fintype.card (Vertices 30000) = 540000 := by
  rw [vertices_card]

-- This is a definition of the broad source assertion, not an axiom or theorem.
def BroadConjecture : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (K : FiniteComplex V),
    Fintype.card V = 2*d → K.Pure d → K.Flag → K.Unimodal d

-- Exact outstanding witness obligation, deliberately not asserted as a theorem.
def MissingWitness : Prop :=
  (graphComplex 30000).Pure 270000 ∧
    ¬ (graphComplex 30000).Unimodal 270000

#print axioms graphComplex
#print axioms graphComplex_flag
#print axioms witness_vertices
end PureFlag
```
<!-- END LEAN MODULE Endpoint -->

<!-- BEGIN LEAN MODULE MixedPurity SHA256 710141d2c97fa34d75dc2e37ae082d406ec3a4e24958dba1b8c6b848e534cb08 -->
```lean
import Purity
import Endpoint
namespace PureFlag
variable {A B V K : Type*}
theorem keyed_rep_max [Fintype K] [DecidableEq V] (k : V → K)
    (rep : K → V) (hr : ∀ i, k (rep i) = i) :
    MaxInd (fun u v => u ≠ v ∧ k u = k v) (Finset.univ.image rep) := by
  classical
  constructor
  · intro u hu v hv ⟨hn,he⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    rw [hr,hr] at he
    exact hn (congrArg rep he)
  · intro t ht hsub
    apply Finset.Subset.antisymm _ hsub
    intro u hu
    have hm : rep (k u) ∈ Finset.univ.image rep := Finset.mem_image.mpr ⟨k u,by simp,rfl⟩
    by_cases he : u = rep (k u)
    · rw [he]; exact hm
    · exact (ht u hu _ (hsub hm) ⟨he,(hr _).symm⟩).elim

noncomputable def branchRep (a p q : ℕ) [NeZero p] [NeZero q] : (Fin a ⊕ Fin a) → Branch a p q
  | .inl i => .inl (i,0)
  | .inr i => .inr (i,0)
@[simp] theorem branch_key_rep (a p q : ℕ) [NeZero p] [NeZero q] (i : Fin a ⊕ Fin a) :
    key (branchRep a p q i) = i := by cases i <;> rfl

theorem branch_max_card (a p q : ℕ) [NeZero p] [NeZero q]
    (s : Finset (Branch a p q)) (hs : MaxInd BranchAdj s) : s.card = 2*a := by
  classical
  have h := keyed_card key (branchRep a p q) (branch_key_rep a p q) s hs
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem max_join_card [DecidableEq A] [DecidableEq B]
    (R : A → A → Prop) (S : B → B → Prop) (d : ℕ)
    (hR : ∀ s, MaxInd R s → s.card = d) (hS : ∀ t, MaxInd S t → t.card = d)
    (u : Finset (A ⊕ B)) (hu : MaxInd (JoinRel R S) u) : u.card = d := by
  have hf := (join_faces R S u.toLeft u.toRight).mp (by rw [Finset.toLeft_disjSum_toRight]; exact hu.1)
  rcases hf.2.2 with hl | hr
  · have ht : MaxInd S u.toRight := by
      refine ⟨hf.2.1, ?_⟩
      intro t ht hsub
      have hh := hu.2 ((∅ : Finset A).disjSum t)
        ((join_faces R S ∅ t).mpr ⟨independent_empty R,ht,Or.inl rfl⟩)
        (Finset.subset_disjSum.mpr ⟨by simp [hl],hsub⟩)
      simpa only [Finset.toRight_disjSum] using congrArg Finset.toRight hh
    rw [split_card, hl, Finset.card_empty, zero_add, hS _ ht]
  · have hs : MaxInd R u.toLeft := by
      refine ⟨hf.1, ?_⟩
      intro s hs hsub
      have hh := hu.2 (s.disjSum (∅ : Finset B))
        ((join_faces R S s ∅).mpr ⟨hs,independent_empty S,Or.inr rfl⟩)
        (Finset.subset_disjSum.mpr ⟨hsub,by simp [hr]⟩)
      simpa only [Finset.toLeft_disjSum] using congrArg Finset.toLeft hh
    rw [split_card, hr, Finset.card_empty, add_zero, hR _ hs]

theorem adj_decomposition (a : ℕ) :
    @Adj a = DisjointRel (JoinRel (@BranchAdj a 1 5) (@BranchAdj a 2 3))
      (fun _ _ : Fin (7*a) => False) := by
  funext u v
  rcases u with (u|u)|u <;> rcases v with (v|v)|v <;> rfl

theorem graph_facet_card (a : ℕ) (s : Finset (Vertices a))
    (hs : (graphComplex a).Facet s) : s.card = 9*a := by
  classical
  have hm : MaxInd Adj s := hs
  rw [adj_decomposition] at hm
  have hh := (max_disjoint _ _ s.toLeft s.toRight).mp (by rw [Finset.toLeft_disjSum_toRight]; exact hm)
  have hl := max_join_card _ _ (2*a) (branch_max_card a 1 5) (branch_max_card a 2 3) s.toLeft hh.1
  have hr : s.toRight = Finset.univ := by
    exact (hh.2.2 Finset.univ (by simp [Independent]) (Finset.subset_univ _)).symm
  rw [split_card, hl, hr]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem graph_pure (a : ℕ) (ha : 0 < a) : (graphComplex a).Pure (9*a) := by
  classical
  let s : Finset (Branch a 1 5) := Finset.univ.image (branchRep a 1 5)
  have hs : MaxInd BranchAdj s := keyed_rep_max key _ (branch_key_rep a 1 5)
  have hn : s.Nonempty := by
    exact ⟨branchRep a 1 5 (.inl ⟨0,ha⟩),Finset.mem_image.mpr ⟨.inl ⟨0,ha⟩,by simp,rfl⟩⟩
  have hj := max_join_left (@BranchAdj a 1 5) (@BranchAdj a 2 3) s hn hs
  have he : MaxInd (fun _ _ : Fin (7*a) => False) Finset.univ := by
    refine ⟨by simp [Independent], ?_⟩
    intro t ht hsub
    exact Finset.Subset.antisymm (Finset.subset_univ _) hsub
  have hm := (max_disjoint _ _ _ _).mpr ⟨hj,he⟩
  rw [← adj_decomposition] at hm
  exact ⟨⟨_,hm⟩,graph_facet_card a⟩

#print axioms keyed_rep_max
#print axioms branch_max_card
#print axioms max_join_card
#print axioms adj_decomposition
#print axioms graph_facet_card
#print axioms graph_pure
end PureFlag
```
<!-- END LEAN MODULE MixedPurity -->

<!-- BEGIN LEAN MODULE GraphPolynomial SHA256 3dfe5a3804f3b5da2dfccfe5602c7078989aff1bbed75ee98416af76fdff1e2a -->
```lean
import FacePolynomial
import ChoiceCounts
import MixedPurity
namespace PureFlag
open scoped BigOperators
open Polynomial
variable {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
abbrev UniformRel (u v : I × T) : Prop := u ≠ v ∧ u.1 = v.1
noncomputable def uniformFaceEquiv : (I → Option T) ≃ Faces (UniformRel (I:=I) (T:=T)) :=
  (choiceEquiv (I:=I) (T:=T)).trans
    { toFun := fun s => ⟨s.val,(partial_iff_independent _).mp s.property⟩
      invFun := fun s => ⟨s.val,(partial_iff_independent _).mpr s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem uniform_polynomial : facePoly (UniformRel (I:=I) (T:=T)) =
    (1 + (Fintype.card T : ℤ[X])*X)^Fintype.card I := by
  classical
  have he : ∀ f : I → Option T,
      (X : ℤ[X])^((uniformFaceEquiv f).val.card) =
        ∏ i : I, if f i ≠ none then X else 1 := by
    intro f
    change X^(encode f).card = _
    rw [encode_card,Finset.prod_ite]
    simp
  have h := Fintype.sum_equiv (uniformFaceEquiv (I:=I) (T:=T))
    (fun f => ∏ i : I, if f i ≠ none then (X : ℤ[X]) else 1)
    (fun s => (X : ℤ[X])^s.val.card) (fun f => (he f).symm)
  unfold facePoly
  rw [← h, ← Fintype.prod_sum (fun (_ : I) (t : Option T) => if t ≠ none then (X : ℤ[X]) else 1)]
  simp [Fintype.sum_option]

theorem branch_decomposition (a p q : ℕ) :
    @BranchAdj a p q = DisjointRel (@UniformRel (Fin a) (Fin p)) (@UniformRel (Fin a) (Fin q)) := by
  funext u v
  rcases u with u|u <;> rcases v with v|v <;>
    simp [BranchAdj,key,DisjointRel,UniformRel]

theorem branch_polynomial (a p q : ℕ) : facePoly (@BranchAdj a p q) =
    ((1 + (p : ℤ[X])*X)*(1+(q : ℤ[X])*X))^a := by
  classical
  rw [branch_decomposition,facePoly_disjoint,uniform_polynomial,uniform_polynomial]
  simp only [Fintype.card_fin,mul_pow]

theorem isolates_polynomial (n : ℕ) : facePoly (fun _ _ : Fin n => False) = (1+X)^n := by
  classical
  let e : Faces (fun _ _ : Fin n => False) ≃ (Fin n → Option Unit) :=
    { toFun := fun s => fun i => if i ∈ s.val then some () else none
      invFun := fun f => ⟨Finset.univ.filter (fun i => f i ≠ none),by simp [Independent]⟩
      left_inv := by intro s; apply Subtype.ext; ext i; simp
      right_inv := by intro f; funext i; cases h : f i with
        | none => simp [h]
        | some u => cases u; simp [h] }
  have h := Fintype.sum_equiv e (fun s => (X : ℤ[X])^s.val.card)
    (fun f => ∏ i : Fin n, if f i ≠ none then (X : ℤ[X]) else 1) (by
      intro s
      simp [e])
  unfold facePoly
  rw [h, ← Fintype.prod_sum (fun (_ : Fin n) (t : Option Unit) => if t ≠ none then (X : ℤ[X]) else 1)]
  simp [Fintype.sum_option]

theorem actual_graph_polynomial (a : ℕ) : facePoly (@Adj a) =
    (1+X)^(7*a) *
      ((((1+X)*(1+5*X))^a) + (((1+2*X)*(1+3*X))^a) - 1) := by
  classical
  rw [adj_decomposition,facePoly_disjoint,facePoly_join,
    branch_polynomial,branch_polynomial,isolates_polynomial]
  norm_num
  ring

#print axioms uniformFaceEquiv
#print axioms uniform_polynomial
#print axioms branch_decomposition
#print axioms branch_polynomial
#print axioms isolates_polynomial
#print axioms actual_graph_polynomial
end PureFlag
```
<!-- END LEAN MODULE GraphPolynomial -->

<!-- BEGIN LEAN MODULE FTransport SHA256 3eeda10ded4661245a01bb096bf092c450d57d53b6cebf324725e0fccb876dc2 -->
```lean
import GraphPolynomial
namespace PureFlag
open Polynomial
noncomputable def allTypesBroadConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], BroadConjecture V

theorem actual_f_coeff (a i : ℕ) :
    ((graphComplex a).f i : ℤ) = (facePoly (@Adj a)).coeff (i+1) := by
  classical
  rw [facePoly_coeff_count]
  let t := (Finset.univ : Finset (Vertices a)).powerset.filter
    (fun s => Independent Adj s ∧ s.card = i+1)
  have ht : ∀ s : Finset (Vertices a), s ∈ t → Independent Adj s ∧ s.card = i+1 := by
    intro s hs; simpa [t] using hs
  let e : {s : Faces (@Adj a) // s.val.card = i+1} ≃ {s // s ∈ t} :=
    { toFun := fun s => ⟨s.val.val,by simp [t,s.val.property,s.property]⟩
      invFun := fun s => ⟨⟨s.val,(ht s.val s.property).1⟩,(ht s.val s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simp only [Fintype.card_coe] at he
  change (t.card : ℤ) = _
  exact congrArg (fun n : ℕ => (n : ℤ)) he.symm

theorem witness_pure : (graphComplex 30000).Pure 270000 := by
  exact graph_pure 30000 (by norm_num)

theorem outer_negation_of_actual_failure
    (h : ¬ (graphComplex 30000).Unimodal 270000) : ¬ allTypesBroadConjecture := by
  intro hc
  exact h (hc (Vertices 30000) 270000 (by norm_num) (graphComplex 30000)
    (by rw [vertices_card]) witness_pure (graphComplex_flag _))

#print axioms allTypesBroadConjecture
#print axioms actual_f_coeff
#print axioms witness_pure
#print axioms outer_negation_of_actual_failure
end PureFlag
```
<!-- END LEAN MODULE FTransport -->

<!-- BEGIN LEAN MODULE GraphBounds SHA256 7e4d67d2774ad6dda9039df81d2d0db7ec2ca7673d1e26b30acb1e008b7f5678 -->
```lean
import FTransport
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
namespace PureFlag
open scoped BigOperators
open Polynomial
variable {V K : Type*}
theorem keyed_bound [Fintype K] (k : V → K) (s : Finset V)
    (hs : Independent (fun u v => u ≠ v ∧ k u = k v) s) : s.card ≤ Fintype.card K := by
  classical
  apply Finset.card_le_card_of_injOn k (fun _ _ => Finset.mem_univ _)
  intro u hu v hv he
  by_contra hn
  exact hs u hu v hv ⟨hn,he⟩

theorem branch_bound (a p q : ℕ) (s : Finset (Branch a p q))
    (hs : Independent BranchAdj s) : s.card ≤ 2*a := by
  have h := keyed_bound key s hs
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  omega

theorem actual_face_bound (a : ℕ) (s : Faces (@Adj a)) : s.val.card ≤ 9*a := by
  classical
  have hh := (congrArg (fun R : Vertices a → Vertices a → Prop => Independent R s.val) (adj_decomposition a)).mp s.property
  have hf := (disjoint_faces _ _ s.val.toLeft s.val.toRight).mp (by rw [Finset.toLeft_disjSum_toRight]; exact hh)
  have hj := (join_faces _ _ s.val.toLeft.toLeft s.val.toLeft.toRight).mp
    (by rw [Finset.toLeft_disjSum_toRight]; exact hf.1)
  have hb1 := branch_bound a 1 5 _ hj.1
  have hb2 := branch_bound a 2 3 _ hj.2.1
  have hi : s.val.toRight.card ≤ 7*a := by simpa using Finset.card_le_univ s.val.toRight
  have h1 := split_card s.val
  have h2 := split_card s.val.toLeft
  rcases hj.2.2 with h | h <;> rw [h,Finset.card_empty] at h2 <;> omega

theorem actual_coeff_nonneg (a n : ℕ) : 0 ≤ (facePoly (@Adj a)).coeff n := by
  rw [facePoly_coeff_count]
  exact Nat.cast_nonneg _

theorem actual_coeff_support (a n : ℕ) (hn : 9*a < n) : (facePoly (@Adj a)).coeff n = 0 := by
  classical
  simp only [facePoly,finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  have he : s.val.card ≠ n := by have := actual_face_bound a s; omega
  simp [Polynomial.coeff_X_pow,Ne.symm he]

def commonMass (a : ℕ) : ℚ := 2^(7*a)*12^a
def emptyMass (a : ℕ) : ℚ := 2^(7*a)
theorem commonMass_pos (a : ℕ) : 0 < commonMass a := by unfold commonMass; positivity

theorem normalized_empty_ratio (a : ℕ) : emptyMass a / commonMass a = 1/(12:ℚ)^a := by
  unfold emptyMass commonMass
  have h : (2:ℚ)^(7*a) ≠ 0 := by positivity
  field_simp

theorem normalized_empty_bound (a : ℕ) (ha : 0 < a) :
    0 < emptyMass a / commonMass a ∧ emptyMass a / commonMass a ≤ 1/12 := by
  rw [normalized_empty_ratio]
  have hp : (12:ℚ) ≤ 12^a := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hh : (1:ℚ) ≤ 12^n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  constructor
  · positivity
  · apply (div_le_div_iff₀ (by positivity : (0:ℚ)<12^a) (by norm_num : (0:ℚ)<12)).mpr
    simpa using hp

theorem exact_window_containment (j : ℤ)
    (h : (144375 ≤ j ∧ j ≤ 145624) ∨ (145625 ≤ j ∧ j ≤ 146874) ∨ (146875 ≤ j ∧ j ≤ 148124)) :
    0 ≤ j-1 ∧ j-1 < 270000 := by omega

#print axioms keyed_bound
#print axioms branch_bound
#print axioms actual_face_bound
#print axioms actual_coeff_nonneg
#print axioms actual_coeff_support
#print axioms commonMass_pos
#print axioms normalized_empty_ratio
#print axioms normalized_empty_bound
#print axioms exact_window_containment
end PureFlag
```
<!-- END LEAN MODULE GraphBounds -->

<!-- BEGIN LEAN MODULE DegreePushforward SHA256 6e0c37ed0ad6dccbaa4331c69bb767a7cdd850f62fd2b83ae655d4bd66602fea -->
```lean
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
namespace PureFlag
open scoped BigOperators
open Polynomial
variable {I J : Type*}
def degreeWeight (s : Finset I) (w : I → ℚ) (d : I → ℕ) (n : ℕ) : ℚ :=
  ∑ i ∈ s with d i = n, w i
noncomputable def degreePoly (s : Finset I) (w : I → ℚ) (d : I → ℕ) : ℚ[X] :=
  ∑ i ∈ s, C (w i) * X^(d i)
theorem degreePoly_coeff (s : Finset I) (w : I → ℚ) (d : I → ℕ) (n : ℕ) :
    (degreePoly s w d).coeff n = degreeWeight s w d n := by
  classical
  simp [degreePoly,degreeWeight,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Finset.sum_filter,eq_comm]

theorem degree_transport (s : Finset I) (w : I → ℚ) (d : I → ℕ) (g : ℕ → ℚ) :
    (∑ n ∈ s.image d, g n * degreeWeight s w d n) = ∑ i ∈ s, g (d i)*w i := by
  classical
  unfold degreeWeight
  simp only [Finset.mul_sum]
  calc
    _ = ∑ n ∈ s.image d, ∑ i ∈ s with d i = n, g (d i)*w i := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem d hi) _

theorem degreeWeight_nonneg (s : Finset I) (w : I → ℚ) (d : I → ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (n : ℕ) : 0 ≤ degreeWeight s w d n := by
  apply Finset.sum_nonneg
  intro i hi
  exact hw i (Finset.mem_filter.mp hi).1

theorem degreeWeight_outside (s : Finset I) (w : I → ℚ) (d : I → ℕ)
    (n : ℕ) (hn : n ∉ s.image d) : degreeWeight s w d n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  exact (hn (he ▸ Finset.mem_image_of_mem d (Finset.mem_filter.mp hi).1)).elim

theorem degreePoly_product (s : Finset I) (t : Finset J)
    (u : I → ℚ) (v : J → ℚ) (d : I → ℕ) (e : J → ℕ) :
    degreePoly (s ×ˢ t) (fun p => u p.1 * v p.2) (fun p => d p.1 + e p.2) =
      degreePoly s u d * degreePoly t v e := by
  classical
  simp only [degreePoly,Finset.sum_product,Finset.sum_mul,Finset.mul_sum,pow_add,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms degreePoly_coeff
#print axioms degree_transport
#print axioms degreeWeight_nonneg
#print axioms degreeWeight_outside
#print axioms degreePoly_product
end PureFlag
```
<!-- END LEAN MODULE DegreePushforward -->

<!-- BEGIN LEAN MODULE Moments SHA256 3eb679fba15997a078a9f7241490fde63e462d173d1196422eb10926e05c5822 -->
```lean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace PureFlag
open scoped BigOperators
variable {ι κ : Type*}

def mass (s : Finset ι) (w : ι → ℚ) : ℚ := ∑ i ∈ s, w i
def first (s : Finset ι) (w x : ι → ℚ) : ℚ := ∑ i ∈ s, x i * w i
def second (s : Finset ι) (w x : ι → ℚ) : ℚ := ∑ i ∈ s, x i ^ 2 * w i

theorem product_mass (s : Finset ι) (t : Finset κ) (u : ι → ℚ) (v : κ → ℚ) :
    (∑ i ∈ s, ∑ j ∈ t, u i * v j) = mass s u * mass t v := by
  simp only [mass, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem product_first (s : Finset ι) (t : Finset κ)
    (u x : ι → ℚ) (v y : κ → ℚ) :
    (∑ i ∈ s, ∑ j ∈ t, (x i + y j) * (u i * v j)) =
      first s u x * mass t v + mass s u * first t v y := by
  simp only [first, mass, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem product_second (s : Finset ι) (t : Finset κ)
    (u x : ι → ℚ) (v y : κ → ℚ) :
    (∑ i ∈ s, ∑ j ∈ t, (x i + y j)^2 * (u i * v j)) =
      second s u x * mass t v + 2 * first s u x * first t v y +
        mass s u * second t v y := by
  simp only [second, first, mass, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finite_chebyshev [DecidableEq ι] (s t : Finset ι)
    (ht : t ⊆ s) (w x : ι → ℚ) (μ r : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (_hr : 0 < r)
    (hout : ∀ i ∈ t, r^2 ≤ (x i - μ)^2) :
    r^2 * (∑ i ∈ t, w i) ≤ ∑ i ∈ s, (x i - μ)^2 * w i := by
  calc
    r^2 * (∑ i ∈ t, w i) = ∑ i ∈ t, r^2 * w i := Finset.mul_sum ..
    _ ≤ ∑ i ∈ t, (x i - μ)^2 * w i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hout i hi) (hw i (ht hi))
    _ ≤ ∑ i ∈ s, (x i - μ)^2 * w i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ht
      intro i hi _
      exact mul_nonneg (sq_nonneg _) (hw i hi)

theorem bernoulli_variance (b : ℚ) (hb : 0 ≤ b) :
    b / (1+b) - (b / (1+b))^2 = b / (1+b)^2 := by
  have h : 1+b ≠ 0 := by linarith
  field_simp [h]
  ring

#print axioms product_mass
#print axioms product_first
#print axioms product_second
#print axioms finite_chebyshev
#print axioms bernoulli_variance
end PureFlag
```
<!-- END LEAN MODULE Moments -->

<!-- BEGIN LEAN MODULE BetaPowers SHA256 0e71a2bf3212d18de3b9fb4fb3db46e81c2097922d230503935a9c8460c6491e -->
```lean
import DegreePushforward
import Moments
namespace PureFlag
open scoped BigOperators
open Polynomial
def betaDegree (t : Bool) : ℕ := if t then 1 else 0
def betaWeight (b : ℚ) (t : Bool) : ℚ := if t then b/(1+b) else 1/(1+b)
abbrev Trials : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Trials n
instance trialsFintype : (n : ℕ) → Fintype (Trials n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd Bool (Trials n) inferInstance (trialsFintype n)
def trialDegree : (n : ℕ) → Trials n → ℕ
  | 0, _ => 0
  | n+1, t => betaDegree t.1 + trialDegree n t.2
def trialWeight (b : ℚ) : (n : ℕ) → Trials n → ℚ
  | 0, _ => 1
  | n+1, t => betaWeight b t.1 * trialWeight b n t.2

theorem beta_moments (b : ℚ) (hb : 0 ≤ b) :
    mass Finset.univ (betaWeight b) = 1 ∧
    first Finset.univ (betaWeight b) (fun t => (betaDegree t : ℚ)) = b/(1+b) ∧
    second Finset.univ (betaWeight b) (fun t => (betaDegree t : ℚ)) = b/(1+b) := by
  have hn : 1+b ≠ 0 := by linarith
  simp [mass,first,second,betaWeight,betaDegree]
  field_simp
  ring

theorem trial_moments (b : ℚ) (hb : 0 ≤ b) (n : ℕ) :
    mass Finset.univ (trialWeight b n) = 1 ∧
    first Finset.univ (trialWeight b n) (fun t => (trialDegree n t : ℚ)) = (n:ℚ)*(b/(1+b)) ∧
    second Finset.univ (trialWeight b n) (fun t => (trialDegree n t : ℚ)) =
      (n:ℚ)*(b/(1+b)^2) + ((n:ℚ)*(b/(1+b)))^2 := by
  induction n with
  | zero => simp [mass,first,second,trialWeight,trialDegree,Trials]
  | succ n ih =>
    have hbeta := beta_moments b hb
    have hm := product_mass (Finset.univ : Finset Bool) (Finset.univ : Finset (Trials n)) (betaWeight b) (trialWeight b n)
    have hf := product_first (Finset.univ : Finset Bool) (Finset.univ : Finset (Trials n))
      (betaWeight b) (fun t => (betaDegree t : ℚ)) (trialWeight b n) (fun t => (trialDegree n t : ℚ))
    have hs := product_second (Finset.univ : Finset Bool) (Finset.univ : Finset (Trials n))
      (betaWeight b) (fun t => (betaDegree t : ℚ)) (trialWeight b n) (fun t => (trialDegree n t : ℚ))
    rw [hbeta.1,ih.1] at hm
    rw [hbeta.1,hbeta.2.1,ih.1,ih.2.1] at hf
    rw [hbeta.1,hbeta.2.1,hbeta.2.2,ih.1,ih.2.1,ih.2.2] at hs
    have hv := bernoulli_variance b hb
    constructor
    · simpa only [mass,trialWeight,Fintype.sum_prod_type,one_mul] using hm
    constructor
    · simp only [first,trialWeight,trialDegree,Nat.cast_add,Fintype.sum_prod_type]
      rw [hf]
      push_cast
      ring
    · simp only [second,trialWeight,trialDegree,Nat.cast_add,Fintype.sum_prod_type]
      rw [hs]
      push_cast
      nlinarith [hv]

theorem trial_polynomial (b : ℚ) (n : ℕ) :
    degreePoly Finset.univ (trialWeight b n) (trialDegree n) =
      (Polynomial.C (1/(1+b)) + Polynomial.C (b/(1+b))*X)^n := by
  classical
  induction n with
  | zero => simp [degreePoly,trialWeight,trialDegree,Trials]
  | succ n ih =>
    change degreePoly ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Trials n)))
      (fun t => betaWeight b t.1 * trialWeight b n t.2)
      (fun t => betaDegree t.1 + trialDegree n t.2) = _
    rw [degreePoly_product,ih]
    change ((∑ t : Bool, C (betaWeight b t) * X^(betaDegree t)) *
      (C (1/(1+b)) + C (b/(1+b))*X)^n) = _
    rw [Fintype.sum_bool]
    norm_num only [betaWeight,betaDegree,Bool.false_eq_true,ite_false,ite_true,pow_zero,pow_one,mul_one]
    rw [pow_succ]
    ring

#print axioms beta_moments
#print axioms trial_moments
#print axioms trial_polynomial
end PureFlag
```
<!-- END LEAN MODULE BetaPowers -->

<!-- BEGIN LEAN MODULE NormalizedPowers SHA256 3769d1d4d0f2fe06cac4160612671be435401f34aeb11ce90dcae538998051f2 -->
```lean
import BetaPowers
namespace PureFlag
open scoped BigOperators
open Polynomial
noncomputable def trialSupport (n : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (trialDegree n)
noncomputable def betaPower (b : ℚ) (n : ℕ) : ℚ[X] :=
  (C (1/(1+b)) + C (b/(1+b))*X)^n

theorem trialWeight_nonneg (b : ℚ) (hb : 0 ≤ b) (n : ℕ) :
    ∀ t : Trials n, 0 ≤ trialWeight b n t := by
  induction n with
  | zero => intro t; exact zero_le_one
  | succ n ih =>
    intro t
    apply mul_nonneg _ (ih t.2)
    unfold betaWeight
    have hd : 0 ≤ 1+b := by linarith
    split_ifs
    · exact div_nonneg hb hd
    · exact div_nonneg zero_le_one hd

theorem betaPower_coeff_nonneg (b : ℚ) (hb : 0 ≤ b) (n j : ℕ) :
    0 ≤ (betaPower b n).coeff j := by
  rw [betaPower,← trial_polynomial,degreePoly_coeff]
  exact degreeWeight_nonneg _ _ _ (fun i _ => trialWeight_nonneg b hb n i) j

theorem betaPower_support (b : ℚ) (n j : ℕ) (hj : j ∉ trialSupport n) :
    (betaPower b n).coeff j = 0 := by
  classical
  rw [betaPower,← trial_polynomial,degreePoly_coeff]
  exact degreeWeight_outside _ _ _ _ hj

theorem betaPower_moments (b : ℚ) (hb : 0 ≤ b) (n : ℕ) :
    (∑ j ∈ trialSupport n, (betaPower b n).coeff j) = 1 ∧
    (∑ j ∈ trialSupport n, (j:ℚ)*(betaPower b n).coeff j) = (n:ℚ)*(b/(1+b)) ∧
    (∑ j ∈ trialSupport n, (j:ℚ)^2*(betaPower b n).coeff j) =
      (n:ℚ)*(b/(1+b)^2) + ((n:ℚ)*(b/(1+b)))^2 := by
  classical
  have hm := degree_transport Finset.univ (trialWeight b n) (trialDegree n) (fun _ => 1)
  have hf := degree_transport Finset.univ (trialWeight b n) (trialDegree n) (fun j => (j:ℚ))
  have hs := degree_transport Finset.univ (trialWeight b n) (trialDegree n) (fun j => (j:ℚ)^2)
  have h := trial_moments b hb n
  simp only [one_mul] at hm
  simp only [betaPower,← trial_polynomial,degreePoly_coeff,trialSupport]
  exact ⟨hm.trans h.1, hf.trans h.2.1, hs.trans h.2.2⟩

#print axioms trialWeight_nonneg
#print axioms betaPower_coeff_nonneg
#print axioms betaPower_support
#print axioms betaPower_moments
end PureFlag
```
<!-- END LEAN MODULE NormalizedPowers -->

<!-- BEGIN LEAN MODULE Heterogeneous SHA256 d38ab1adf184b0c94b1fc5185213f33e9a8fbecd3133453978844a1d65c99388 -->
```lean
import NormalizedPowers
namespace PureFlag
open scoped BigOperators
open Polynomial
variable {I J : Type*} [Fintype I] [Fintype J]

theorem heterogeneous_moments (u : I → ℚ) (d : I → ℕ) (v : J → ℚ) (e : J → ℕ)
    (μ ν σ τ : ℚ)
    (hu : mass Finset.univ u = 1 ∧ first Finset.univ u (fun i => (d i : ℚ)) = μ ∧
      second Finset.univ u (fun i => (d i : ℚ)) = σ + μ^2)
    (hv : mass Finset.univ v = 1 ∧ first Finset.univ v (fun j => (e j : ℚ)) = ν ∧
      second Finset.univ v (fun j => (e j : ℚ)) = τ + ν^2) :
    mass Finset.univ (fun p : I × J => u p.1 * v p.2) = 1 ∧
    first Finset.univ (fun p : I × J => u p.1 * v p.2)
      (fun p => ((d p.1 + e p.2 : ℕ) : ℚ)) = μ + ν ∧
    second Finset.univ (fun p : I × J => u p.1 * v p.2)
      (fun p => ((d p.1 + e p.2 : ℕ) : ℚ)) = (σ+τ) + (μ+ν)^2 := by
  have hm := product_mass Finset.univ Finset.univ u v
  have hf := product_first Finset.univ Finset.univ u (fun i => (d i : ℚ)) v (fun j => (e j : ℚ))
  have hs := product_second Finset.univ Finset.univ u (fun i => (d i : ℚ)) v (fun j => (e j : ℚ))
  rw [hu.1,hv.1] at hm
  rw [hu.1,hv.1,hu.2.1,hv.2.1] at hf
  rw [hu.1,hv.1,hu.2.1,hv.2.1,hu.2.2,hv.2.2] at hs
  constructor
  · simpa only [mass,Fintype.sum_prod_type,mul_one] using hm
  constructor
  · simpa only [first,Fintype.sum_prod_type,Nat.cast_add,mul_one,one_mul] using hf
  · simp only [second,Fintype.sum_prod_type,Nat.cast_add]
    rw [hs]
    ring

noncomputable def mixedWeight (a : ℕ) (t : Trials (8*a) × Trials a) : ℚ :=
  trialWeight 1 (8*a) t.1 * trialWeight 5 a t.2
def mixedDegree (a : ℕ) (t : Trials (8*a) × Trials a) : ℕ :=
  trialDegree (8*a) t.1 + trialDegree a t.2

theorem first_branch_moments (a : ℕ) :
    mass Finset.univ (mixedWeight a) = 1 ∧
    first Finset.univ (mixedWeight a) (fun t => (mixedDegree a t : ℚ)) = 29*(a:ℚ)/6 ∧
    second Finset.univ (mixedWeight a) (fun t => (mixedDegree a t : ℚ)) =
      77*(a:ℚ)/36 + (29*(a:ℚ)/6)^2 := by
  have h := heterogeneous_moments _ _ _ _ _ _ _ _
    (trial_moments 1 (by norm_num) (8*a)) (trial_moments 5 (by norm_num) a)
  refine ⟨h.1, h.2.1.trans ?_, h.2.2.trans ?_⟩
  · push_cast
    ring
  · push_cast
    ring

theorem first_branch_polynomial (a : ℕ) :
    degreePoly Finset.univ (mixedWeight a) (mixedDegree a) = betaPower 1 (8*a) * betaPower 5 a := by
  classical
  change degreePoly (Finset.univ ×ˢ Finset.univ) _ _ = _
  unfold mixedWeight mixedDegree
  rw [degreePoly_product,trial_polynomial,trial_polynomial]
  rfl

#print axioms heterogeneous_moments
#print axioms first_branch_moments
#print axioms first_branch_polynomial
end PureFlag
```
<!-- END LEAN MODULE Heterogeneous -->

<!-- BEGIN LEAN MODULE SecondBranch SHA256 4c7f302e7c90077fb4740beb435204ee77c966ac3b7a5f401820cc0f5fd8422d -->
```lean
import Heterogeneous
namespace PureFlag
open scoped BigOperators
open Polynomial
noncomputable def innerWeight (a : ℕ) (t : Trials (7*a) × Trials a) : ℚ :=
  trialWeight 1 (7*a) t.1 * trialWeight 2 a t.2
def innerDegree (a : ℕ) (t : Trials (7*a) × Trials a) : ℕ :=
  trialDegree (7*a) t.1 + trialDegree a t.2
noncomputable def secondWeight (a : ℕ) (t : (Trials (7*a) × Trials a) × Trials a) : ℚ :=
  innerWeight a t.1 * trialWeight 3 a t.2
def secondDegree (a : ℕ) (t : (Trials (7*a) × Trials a) × Trials a) : ℕ :=
  innerDegree a t.1 + trialDegree a t.2

theorem second_branch_moments (a : ℕ) :
    mass Finset.univ (secondWeight a) = 1 ∧
    first Finset.univ (secondWeight a) (fun t => (secondDegree a t : ℚ)) = 59*(a:ℚ)/12 ∧
    second Finset.univ (secondWeight a) (fun t => (secondDegree a t : ℚ)) =
      311*(a:ℚ)/144 + (59*(a:ℚ)/12)^2 := by
  have hi := heterogeneous_moments _ _ _ _ _ _ _ _
    (trial_moments 1 (by norm_num) (7*a)) (trial_moments 2 (by norm_num) a)
  have hi' : mass Finset.univ (innerWeight a) = 1 ∧
      first Finset.univ (innerWeight a) (fun t => (innerDegree a t : ℚ)) =
        (7*(a:ℚ)/2+2*(a:ℚ)/3) ∧
      second Finset.univ (innerWeight a) (fun t => (innerDegree a t : ℚ)) =
        (7*(a:ℚ)/4+2*(a:ℚ)/9)+(7*(a:ℚ)/2+2*(a:ℚ)/3)^2 := by
    refine ⟨hi.1,hi.2.1.trans ?_,hi.2.2.trans ?_⟩ <;> push_cast <;> ring
  have h := heterogeneous_moments _ _ _ _ _ _ _ _ hi' (trial_moments 3 (by norm_num) a)
  refine ⟨h.1,h.2.1.trans ?_,h.2.2.trans ?_⟩ <;> ring

theorem second_branch_polynomial (a : ℕ) :
    degreePoly Finset.univ (secondWeight a) (secondDegree a) =
      betaPower 1 (7*a) * betaPower 2 a * betaPower 3 a := by
  classical
  change degreePoly (Finset.univ ×ˢ Finset.univ) _ _ = _
  unfold secondWeight secondDegree
  rw [degreePoly_product,trial_polynomial]
  change degreePoly (Finset.univ ×ˢ Finset.univ) _ _ * _ = _
  unfold innerWeight innerDegree
  rw [degreePoly_product,trial_polynomial,trial_polynomial]
  rfl
#print axioms second_branch_moments
#print axioms second_branch_polynomial
end PureFlag
```
<!-- END LEAN MODULE SecondBranch -->

<!-- BEGIN LEAN MODULE Variance SHA256 055fc8cb03358e8711e64f4af0f3a9bebb7fce5cb0f3091a077b2115a0caa76b -->
```lean
import Moments

namespace PureFlag
open scoped BigOperators
variable {ι κ : Type*}

theorem centered_second (s : Finset ι) (w x : ι → ℚ) (μ : ℚ) :
    (∑ i ∈ s, (x i - μ)^2 * w i) =
      second s w x - 2*μ*first s w x + μ^2*mass s w := by
  simp only [second, first, mass, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem product_centered_variance (s : Finset ι) (t : Finset κ)
    (u x : ι → ℚ) (v y : κ → ℚ)
    (hu : mass s u = 1) (hv : mass t v = 1) :
    (∑ i ∈ s, ∑ j ∈ t,
      (x i + y j - (first s u x + first t v y))^2 * (u i * v j)) =
    (second s u x - (first s u x)^2) +
      (second t v y - (first t v y)^2) := by
  have hex : ∀ i j,
      (x i + y j - (first s u x + first t v y))^2 * (u i * v j) =
      (x i+y j)^2*(u i*v j) -
        2*(first s u x+first t v y)*((x i+y j)*(u i*v j)) +
        (first s u x+first t v y)^2*(u i*v j) := by
    intro i j; ring
  simp_rw [hex]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [product_second, product_first, ← Finset.sum_mul]
  simp only [mass] at hu hv ⊢
  rw [hu, hv]
  ring

#print axioms centered_second
#print axioms product_centered_variance
end PureFlag
```
<!-- END LEAN MODULE Variance -->

<!-- BEGIN LEAN MODULE MixedCoefficients SHA256 df49d2576d8b4c8c40cc518c6a319980f6c433d63fdd04539da32c24bf1f1f98 -->
```lean
import SecondBranch
import Variance
namespace PureFlag
open scoped BigOperators
open Polynomial
variable {I : Type*} [Fintype I]
theorem coefficient_centered (u : I → ℚ) (d : I → ℕ) (P : ℚ[X]) (μ σ : ℚ)
    (hp : degreePoly Finset.univ u d = P)
    (h : mass Finset.univ u = 1 ∧ first Finset.univ u (fun i => (d i : ℚ)) = μ ∧
      second Finset.univ u (fun i => (d i : ℚ)) = σ + μ^2) :
    (∑ j ∈ Finset.univ.image d, P.coeff j) = 1 ∧
    (∑ j ∈ Finset.univ.image d, (j:ℚ) * P.coeff j) = μ ∧
    (∑ j ∈ Finset.univ.image d, ((j:ℚ)-μ)^2 * P.coeff j) = σ := by
  classical
  have hm := degree_transport Finset.univ u d (fun _ => 1)
  have hf := degree_transport Finset.univ u d (fun j => (j:ℚ))
  have hv := degree_transport Finset.univ u d (fun j => ((j:ℚ)-μ)^2)
  rw [← hp]
  simp only [degreePoly_coeff]
  simp only [one_mul] at hm
  refine ⟨hm.trans h.1,hf.trans h.2.1,hv.trans ?_⟩
  rw [centered_second,h.1,h.2.1,h.2.2]
  ring

theorem first_coefficients (a : ℕ) :
    (∑ j ∈ Finset.univ.image (mixedDegree a),
      (betaPower 1 (8*a) * betaPower 5 a).coeff j) = 1 ∧
    (∑ j ∈ Finset.univ.image (mixedDegree a), (j:ℚ) *
      (betaPower 1 (8*a) * betaPower 5 a).coeff j) = 29*(a:ℚ)/6 ∧
    (∑ j ∈ Finset.univ.image (mixedDegree a), ((j:ℚ)-29*(a:ℚ)/6)^2 *
      (betaPower 1 (8*a) * betaPower 5 a).coeff j) = 77*(a:ℚ)/36 :=
  coefficient_centered _ _ _ _ _ (first_branch_polynomial a) (first_branch_moments a)

theorem second_coefficients (a : ℕ) :
    (∑ j ∈ Finset.univ.image (secondDegree a),
      (betaPower 1 (7*a) * betaPower 2 a * betaPower 3 a).coeff j) = 1 ∧
    (∑ j ∈ Finset.univ.image (secondDegree a), (j:ℚ) *
      (betaPower 1 (7*a) * betaPower 2 a * betaPower 3 a).coeff j) = 59*(a:ℚ)/12 ∧
    (∑ j ∈ Finset.univ.image (secondDegree a), ((j:ℚ)-59*(a:ℚ)/12)^2 *
      (betaPower 1 (7*a) * betaPower 2 a * betaPower 3 a).coeff j) = 311*(a:ℚ)/144 :=
  coefficient_centered _ _ _ _ _ (second_branch_polynomial a) (second_branch_moments a)

#print axioms coefficient_centered
#print axioms first_coefficients
#print axioms second_coefficients
end PureFlag
```
<!-- END LEAN MODULE MixedCoefficients -->

<!-- BEGIN LEAN MODULE BranchScaling SHA256 622a5ea7d805df7566e31742f9df2c161353565fc3a38e03bec572c31e06556c -->
```lean
import MixedCoefficients
namespace PureFlag
open Polynomial

theorem beta_factor (b : ℚ) (hb : 1+b ≠ 0) :
    C (1+b) * (C (1/(1+b)) + C (b/(1+b))*X) = 1+C b*X := by
  calc
    _ = C ((1+b)*(1/(1+b))) + C ((1+b)*(b/(1+b)))*X := by
      simp only [map_mul]
      ring
    _ = _ := by
      have h1 : (1+b)*(1/(1+b)) = 1 := by field_simp
      have h2 : (1+b)*(b/(1+b)) = b := by field_simp
      rw [h1,h2,map_one]

theorem beta_power_scale (b : ℚ) (hb : 1+b ≠ 0) (n : ℕ) :
    C ((1+b)^n) * betaPower b n = (1+C b*X)^n := by
  rw [betaPower,map_pow,← mul_pow,beta_factor b hb]

noncomputable def rawFirst (a : ℕ) : ℚ[X] := (1+X)^(8*a)*(1+5*X)^a
noncomputable def rawSecond (a : ℕ) : ℚ[X] := (1+X)^(7*a)*(1+2*X)^a*(1+3*X)^a

theorem first_scale (a : ℕ) :
    C ((2:ℚ)^(7*a)*12^a) * (betaPower 1 (8*a)*betaPower 5 a) = rawFirst a := by
  have hm : (2:ℚ)^(7*a)*12^a = 2^(8*a)*6^a := by
    rw [show 8*a=7*a+a by omega,pow_add]
    rw [show (12:ℚ)=2*6 by norm_num,mul_pow]
    ring
  rw [hm,map_mul]
  calc
    _ = (C ((1+1:ℚ)^(8*a))*betaPower 1 (8*a)) *
        (C ((1+5:ℚ)^a)*betaPower 5 a) := by norm_num; ring
    _ = _ := by rw [beta_power_scale 1 (by norm_num),beta_power_scale 5 (by norm_num)]; simp only [rawFirst,map_one,map_ofNat,one_mul]

theorem second_scale (a : ℕ) :
    C ((2:ℚ)^(7*a)*12^a) * (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a) = rawSecond a := by
  rw [show (12:ℚ)=3*4 by norm_num,mul_pow,map_mul,map_mul]
  calc
    _ = (C ((1+1:ℚ)^(7*a))*betaPower 1 (7*a)) *
        (C ((1+2:ℚ)^a)*betaPower 2 a) * (C ((1+3:ℚ)^a)*betaPower 3 a) := by norm_num; ring
    _ = _ := by rw [beta_power_scale 1 (by norm_num),beta_power_scale 2 (by norm_num),beta_power_scale 3 (by norm_num)]; simp only [rawSecond,map_one,map_ofNat,one_mul]

#print axioms beta_power_scale
#print axioms first_scale
#print axioms second_scale
end PureFlag
```
<!-- END LEAN MODULE BranchScaling -->

<!-- BEGIN LEAN MODULE ActualNormalization SHA256 e7a5b47ce905d4893e4ee575215e64a7761ca5ad170f25c428773cfc6c71f212 -->
```lean
import GraphBounds
import BranchScaling
import Mathlib.Algebra.Polynomial.Eval.Defs
namespace PureFlag
open Polynomial
noncomputable def actualRat (a : ℕ) : ℚ[X] :=
  (facePoly (@Adj a)).map (Int.castRingHom ℚ)

theorem actual_mass_at_one_v3 (a : ℕ) :
    (facePoly (@Adj a)).eval 1 = 2*(2:ℤ)^(7*a)*12^a - 2^(7*a) := by
  rw [actual_graph_polynomial]
  norm_num
  ring

theorem actual_rat_decomposition (a : ℕ) :
    actualRat a = rawFirst a + rawSecond a - (1+X)^(7*a) := by
  unfold actualRat
  rw [actual_graph_polynomial]
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_one,Polynomial.map_X,Polynomial.map_ofNat]
  unfold rawFirst rawSecond
  rw [show 8*a=7*a+a by omega,pow_add,mul_pow,mul_pow]
  ring

theorem actual_normalization (a : ℕ) :
    actualRat a = C (commonMass a) *
      (betaPower 1 (8*a)*betaPower 5 a + betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a) -
      C (emptyMass a)*betaPower 1 (7*a) := by
  rw [mul_add,show C (commonMass a) * (betaPower 1 (8*a)*betaPower 5 a) = rawFirst a from first_scale a,
    show C (commonMass a) * (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a) = rawSecond a from second_scale a]
  have h := beta_power_scale 1 (by norm_num) (7*a)
  norm_num only [one_add_one_eq_two,map_one,one_mul] at h
  change actualRat a = rawFirst a + rawSecond a - C ((2:ℚ)^(7*a))*betaPower 1 (7*a)
  rw [h,actual_rat_decomposition]

theorem actual_normalized_coefficient (a j : ℕ) :
    (actualRat a).coeff j / commonMass a =
      (betaPower 1 (8*a)*betaPower 5 a).coeff j +
      (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a).coeff j -
      (emptyMass a/commonMass a)*(betaPower 1 (7*a)).coeff j := by
  rw [actual_normalization]
  simp only [coeff_sub,coeff_add,coeff_C_mul]
  field_simp [ne_of_gt (commonMass_pos a)]

#print axioms actual_mass_at_one_v3
#print axioms actual_rat_decomposition
#print axioms actual_normalization
#print axioms actual_normalized_coefficient
end PureFlag
```
<!-- END LEAN MODULE ActualNormalization -->

<!-- BEGIN LEAN MODULE RangeMoments SHA256 5951bf4e7906b22365fe6c96ba6a062c612796ada25492efb3b2543762b11b8e -->
```lean
import ActualNormalization
namespace PureFlag
open scoped BigOperators
open Polynomial

theorem trialDegree_le (n : ℕ) (t : Trials n) : trialDegree n t ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := ih t.2
    have hb : betaDegree t.1 ≤ 1 := by unfold betaDegree; split_ifs <;> omega
    change betaDegree t.1 + trialDegree n t.2 ≤ n+1
    omega

variable {I : Type*} [Fintype I]
theorem range_centered (u : I → ℚ) (d : I → ℕ) (P : ℚ[X]) (μ σ : ℚ) (N : ℕ)
    (hp : degreePoly Finset.univ u d = P) (hd : ∀ i, d i ≤ N)
    (hu : ∀ i, 0 ≤ u i)
    (h : mass Finset.univ u = 1 ∧ first Finset.univ u (fun i => (d i : ℚ)) = μ ∧
      second Finset.univ u (fun i => (d i : ℚ)) = σ+μ^2) :
    (∑ j ∈ Finset.range (N+1), P.coeff j) = 1 ∧
    (∑ j ∈ Finset.range (N+1), ((j:ℚ)-μ)^2 * P.coeff j) = σ ∧
    (∀ j, 0 ≤ P.coeff j) := by
  classical
  have hc := coefficient_centered u d P μ σ hp h
  have hz (j : ℕ) (hj : j ∉ Finset.univ.image d) : P.coeff j = 0 := by
    rw [← hp,degreePoly_coeff]
    exact degreeWeight_outside _ _ _ _ hj
  have hs : Finset.univ.image d ⊆ Finset.range (N+1) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by have := hd i; omega)
  have ht (g : ℕ → ℚ) :
      (∑ j ∈ Finset.univ.image d, g j * P.coeff j) =
      ∑ j ∈ Finset.range (N+1), g j * P.coeff j := by
    apply Finset.sum_subset hs
    intro j _ hj
    rw [hz j hj,mul_zero]
  constructor
  · have hm := ht (fun _ => 1)
    simp only [one_mul] at hm
    exact hm.symm.trans hc.1
  constructor
  · exact (ht (fun j => ((j:ℚ)-μ)^2)).symm.trans hc.2.2
  · intro j
    rw [← hp,degreePoly_coeff]
    exact degreeWeight_nonneg _ _ _ (fun i _ => hu i) j

theorem first_range (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), (betaPower 1 (8*a)*betaPower 5 a).coeff j) = 1 ∧
    (∑ j ∈ Finset.range (9*a+1), ((j:ℚ)-29*(a:ℚ)/6)^2 *
      (betaPower 1 (8*a)*betaPower 5 a).coeff j) = 77*(a:ℚ)/36 ∧
    (∀ j, 0 ≤ (betaPower 1 (8*a)*betaPower 5 a).coeff j) := by
  apply range_centered _ _ _ _ _ _ (first_branch_polynomial a) _ _ (first_branch_moments a)
  · intro t
    have h1 := trialDegree_le (8*a) t.1
    have h2 := trialDegree_le a t.2
    unfold mixedDegree
    omega
  · intro t
    exact mul_nonneg (trialWeight_nonneg 1 (by norm_num) _ _) (trialWeight_nonneg 5 (by norm_num) _ _)

theorem second_range (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a).coeff j) = 1 ∧
    (∑ j ∈ Finset.range (9*a+1), ((j:ℚ)-59*(a:ℚ)/12)^2 *
      (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a).coeff j) = 311*(a:ℚ)/144 ∧
    (∀ j, 0 ≤ (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a).coeff j) := by
  apply range_centered _ _ _ _ _ _ (second_branch_polynomial a) _ _ (second_branch_moments a)
  · intro t
    have h1 := trialDegree_le (7*a) t.1.1
    have h2 := trialDegree_le a t.1.2
    have h3 := trialDegree_le a t.2
    unfold secondDegree innerDegree
    omega
  · intro t
    exact mul_nonneg (mul_nonneg (trialWeight_nonneg 1 (by norm_num) _ _)
      (trialWeight_nonneg 2 (by norm_num) _ _)) (trialWeight_nonneg 3 (by norm_num) _ _)

#print axioms trialDegree_le
#print axioms first_range
#print axioms second_range
end PureFlag
```
<!-- END LEAN MODULE RangeMoments -->

<!-- BEGIN LEAN MODULE ActualDistribution SHA256 4a623950b2306e059ee9f91efaf3704b9461fb054267c7f89baaa685a762b609 -->
```lean
import RangeMoments
import Mathlib.Algebra.Polynomial.Eval.Coeff
namespace PureFlag
open scoped BigOperators
open Polynomial
noncomputable def actualW (a j : ℕ) : ℚ := (actualRat a).coeff j / commonMass a

theorem empty_range (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), (betaPower 1 (7*a)).coeff j) = 1 := by
  have h := range_centered (trialWeight 1 (7*a)) (trialDegree (7*a)) (betaPower 1 (7*a))
    _ _ (9*a) (trial_polynomial 1 (7*a))
    (fun t => by have := trialDegree_le (7*a) t; omega)
    (fun t => trialWeight_nonneg 1 (by norm_num) _ t) (trial_moments 1 (by norm_num) (7*a))
  exact h.1

theorem actualW_nonneg (a j : ℕ) : 0 ≤ actualW a j := by
  have hc : 0 ≤ (actualRat a).coeff j := by
    simp only [actualRat,coeff_map]
    change (0:ℚ) ≤ ((facePoly (@Adj a)).coeff j : ℚ)
    exact_mod_cast actual_coeff_nonneg a j
  exact div_nonneg hc (le_of_lt (commonMass_pos a))

theorem actualW_support (a j : ℕ) (hj : 9*a < j) : actualW a j = 0 := by
  unfold actualW actualRat
  rw [coeff_map,actual_coeff_support a j hj]
  simp

theorem actualW_total (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), actualW a j) = 2-emptyMass a/commonMass a := by
  simp only [actualW,actual_normalized_coefficient,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,← Finset.mul_sum]
  rw [(first_range a).1,(second_range a).1,empty_range]
  ring

theorem actual_first_branch_mass (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), (rawFirst a).coeff j) = commonMass a := by
  rw [← first_scale]
  simp only [coeff_C_mul,← Finset.mul_sum,(first_range a).1,mul_one]
  rfl

theorem actual_second_branch_mass (a : ℕ) :
    (∑ j ∈ Finset.range (9*a+1), (rawSecond a).coeff j) = commonMass a := by
  rw [← second_scale]
  simp only [coeff_C_mul,← Finset.mul_sum,(second_range a).1,mul_one]
  rfl

#print axioms empty_range
#print axioms actualW_nonneg
#print axioms actualW_support
#print axioms actualW_total
#print axioms actual_first_branch_mass
#print axioms actual_second_branch_mass
end PureFlag
```
<!-- END LEAN MODULE ActualDistribution -->

<!-- BEGIN LEAN MODULE ChebyshevBlocks SHA256 8eeaff2c87f2566a903032f30530556036e3023f375c9d530ccd63ae1b70f2a0 -->
```lean
import ActualDistribution
import Mathlib.Order.Interval.Finset.Nat
namespace PureFlag
open scoped BigOperators
open Polynomial
abbrev D (a : ℕ) : Finset ℕ := Finset.range (9*a+1)
abbrev B (s : ℕ) : Finset ℕ := Finset.Ico s (s+1250)
noncomputable def p1 (a j : ℕ) : ℚ := (betaPower 1 (8*a)*betaPower 5 a).coeff j
noncomputable def p2 (a j : ℕ) : ℚ := (betaPower 1 (7*a)*betaPower 2 a*betaPower 3 a).coeff j
noncomputable def p0 (a j : ℕ) : ℚ := (betaPower 1 (7*a)).coeff j

theorem cheb_block (a : ℕ) (p : ℕ → ℚ) (s : Finset ℕ) (μ v : ℚ) (hs : s ⊆ D a)
    (hp : ∀ j ∈ D a, 0 ≤ p j) (hm : (∑ j ∈ D a,p j)=1)
    (hv : (∑ j ∈ D a,((j:ℚ)-μ)^2*p j)=v)
    (ho : ∀ j ∈ D a, j ∉ s → (625:ℚ)^2 ≤ ((j:ℚ)-μ)^2) :
    1-v/625^2 ≤ ∑ j ∈ s,p j := by
  have hc := finite_chebyshev (D a) (D a \ s) Finset.sdiff_subset p (fun j => (j:ℚ)) μ 625 hp
    (by norm_num) (fun j hj => ho j (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2)
  rw [hv] at hc
  have ht : (∑ j ∈ D a \ s,p j)+(∑ j ∈ s,p j) = ∑ j ∈ D a,p j := Finset.sum_sdiff hs
  rw [hm] at ht
  norm_num at hc ⊢
  linarith

theorem left_concentration (a : ℕ) (ha : a=30000) : 1-308/1875 ≤ ∑ j ∈ B 144375,p1 a j := by
  have h := first_range a
  rw [show 29*(a:ℚ)/6=145000 by rw [ha]; norm_num, show 77*(a:ℚ)/36=192500/3 by rw [ha]; norm_num] at h
  have hh := cheb_block a (p1 a) (B 144375) 145000 (192500/3)
    (by intro j hj; simp only [B,Finset.mem_Ico] at hj; simp only [D,Finset.mem_range]; omega)
    (fun j _ => h.2.2 j) h.1
    h.2.1 ?_
  · convert hh using 1
    norm_num
  · intro j _ hj
    have hj' : j < 144375 ∨ 145625 ≤ j := by simpa only [B,Finset.mem_Ico,not_and_or,not_le,not_lt] using hj
    rcases hj' with hj'|hj'
    · have hjq : (j:ℚ) ≤ 144374 := by exact_mod_cast (show j ≤ 144374 by omega)
      nlinarith [sq_nonneg ((j:ℚ)-145000+625)]
    · have hjq : (145625:ℚ) ≤ j := by exact_mod_cast hj'
      nlinarith [sq_nonneg ((j:ℚ)-145000-625)]

theorem right_concentration (a : ℕ) (ha : a=30000) : 1-311/1875 ≤ ∑ j ∈ B 146875,p2 a j := by
  have h := second_range a
  rw [show 59*(a:ℚ)/12=147500 by rw [ha]; norm_num, show 311*(a:ℚ)/144=194375/3 by rw [ha]; norm_num] at h
  have hh := cheb_block a (p2 a) (B 146875) 147500 (194375/3)
    (by intro j hj; simp only [B,Finset.mem_Ico] at hj; simp only [D,Finset.mem_range]; omega)
    (fun j _ => h.2.2 j) h.1
    h.2.1 ?_
  · convert hh using 1
    norm_num
  · intro j _ hj
    have hj' : j < 146875 ∨ 148125 ≤ j := by simpa only [B,Finset.mem_Ico,not_and_or,not_le,not_lt] using hj
    rcases hj' with hj'|hj'
    · have hjq : (j:ℚ) ≤ 146874 := by exact_mod_cast (show j ≤ 146874 by omega)
      nlinarith [sq_nonneg ((j:ℚ)-147500+625)]
    · have hjq : (148125:ℚ) ≤ j := by exact_mod_cast hj'
      nlinarith [sq_nonneg ((j:ℚ)-147500-625)]
#print axioms cheb_block
#print axioms left_concentration
#print axioms right_concentration
end PureFlag
```
<!-- END LEAN MODULE ChebyshevBlocks -->

<!-- BEGIN LEAN MODULE ActualBlocks SHA256 c895534a54c1ddf528324c4f18167250475db68e8fb10de654ba069b67d800a8 -->
```lean
import ChebyshevBlocks
namespace PureFlag
open scoped BigOperators
noncomputable def blockMass (a s : ℕ) : ℚ := ∑ j ∈ B s,actualW a j

theorem block_subset (a s : ℕ) (ha : a=30000) (hs : s+1250 ≤ 270001) : B s ⊆ D a := by
  intro j hj
  simp only [B,Finset.mem_Ico] at hj
  simp only [D,Finset.mem_range]
  omega

theorem block_bounds (a s : ℕ) (ha : a=30000) (hs : s+1250 ≤ 270001) :
    (∑ j ∈ B s,p1 a j)-emptyMass a/commonMass a ≤ blockMass a s ∧
    (∑ j ∈ B s,p2 a j)-emptyMass a/commonMass a ≤ blockMass a s := by
  have hp0 : (∑ j ∈ B s,p0 a j) ≤ 1 := by
    rw [← empty_range a]
    apply Finset.sum_le_sum_of_subset_of_nonneg (block_subset a s ha hs)
    intro j _ _
    exact betaPower_coeff_nonneg 1 (by norm_num) _ _
  have hp1 : 0 ≤ ∑ j ∈ B s,p1 a j := Finset.sum_nonneg (fun j _ => (first_range a).2.2 j)
  have hp2 : 0 ≤ ∑ j ∈ B s,p2 a j := Finset.sum_nonneg (fun j _ => (second_range a).2.2 j)
  have hq : 0 ≤ emptyMass a/commonMass a := div_nonneg (by unfold emptyMass; positivity) (le_of_lt (commonMass_pos a))
  have he : blockMass a s = (∑ j ∈ B s,p1 a j)+(∑ j ∈ B s,p2 a j)-
      (emptyMass a/commonMass a)*(∑ j ∈ B s,p0 a j) := by
    simp only [blockMass,actualW,actual_normalized_coefficient,p1,p2,p0,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  have hprod := mul_le_mul_of_nonneg_left hp0 hq
  rw [he]
  constructor <;> linarith only [hprod,hp1,hp2]

theorem middle_bound (a : ℕ) (ha : a=30000) :
    blockMass a 145625 ≤ (2-emptyMass a/commonMass a)-blockMass a 144375-blockMass a 146875 := by
  have h12 : Disjoint (B 144375) (B 145625) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [B,Finset.mem_Ico] at hj hk
    omega
  have h123 : Disjoint (B 144375 ∪ B 145625) (B 146875) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_union,B,Finset.mem_Ico] at hj hk
    omega
  have hs : (B 144375 ∪ B 145625) ∪ B 146875 ⊆ D a := by
    intro j hj
    simp only [Finset.mem_union] at hj
    rcases hj with (hj|hj)|hj
    · exact block_subset a 144375 ha (by norm_num) hj
    · exact block_subset a 145625 ha (by norm_num) hj
    · exact block_subset a 146875 ha (by norm_num) hj
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => actualW_nonneg a j)
  rw [Finset.sum_union h123,Finset.sum_union h12,actualW_total] at hh
  change blockMass a 144375+blockMass a 145625+blockMass a 146875 ≤ _ at hh
  linarith

theorem actual_block_valley (a : ℕ) (ha : a=30000) :
    blockMass a 145625 < blockMass a 144375 ∧ blockMass a 145625 < blockMass a 146875 := by
  have h1 := (block_bounds a 144375 ha (by norm_num)).1
  have h3 := (block_bounds a 146875 ha (by norm_num)).2
  have hc1 := left_concentration a ha
  have hc3 := right_concentration a ha
  have hq := (normalized_empty_bound a (by omega)).2
  apply rational_block_valley (emptyMass a/commonMass a) _ _ _ hq
  · linarith
  · linarith
  · exact middle_bound a ha
#print axioms block_bounds
#print axioms middle_bound
#print axioms actual_block_valley
end PureFlag
```
<!-- END LEAN MODULE ActualBlocks -->

<!-- BEGIN LEAN MODULE Windows SHA256 6864368ce5114d38eb2dad1ccd9dba816ce5cfe1de8429b92041af00328db17c -->
```lean
import Valley
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PureFlag
open scoped BigOperators

def window (u : ℤ → ℚ) (s : ℤ) (L : ℕ) : ℚ :=
  ∑ i ∈ Finset.range L, u (s + (i : ℤ))

theorem window_step (u : ℤ → ℚ) (s : ℤ) (L : ℕ) :
    window u (s+1) L - window u s L = u (s+(L:ℤ)) - u s := by
  induction L with
  | zero => simp [window]
  | succ n ih =>
    simp only [window, Finset.sum_range_succ] at *
    have h : s + 1 + (n : ℤ) = s + (n : ℤ) + 1 := by omega
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    rw [h]
    linarith

theorem exists_drop (H : ℤ → ℚ) (a : ℤ) (n : ℕ)
    (h : H (a+(n:ℤ)) < H a) :
    ∃ i : ℕ, i < n ∧ H (a+(i:ℤ)+1) < H (a+(i:ℤ)) := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    by_cases hd : H (a+(n:ℤ)+1) < H (a+(n:ℤ))
    · exact ⟨n, Nat.lt_succ_self n, hd⟩
    · have he : H (a+(n:ℤ)) < H a := by
        simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at h
        linarith
      obtain ⟨i, hi, hv⟩ := ih he
      exact ⟨i, by omega, hv⟩

theorem window_valley_not_mode (u : ℤ → ℚ) (s : ℤ) (L : ℕ)
    (hl : window u (s+(L:ℤ)) L < window u s L)
    (hr : window u (s+(L:ℤ)) L < window u (s+(L:ℤ)+(L:ℤ)) L) :
    ¬ HasMode u := by
  intro hu
  obtain ⟨i, hi, hdrop⟩ := exists_drop (fun t => window u t L) s L hl
  have hn : (-window u (s+(L:ℤ)+(L:ℤ)) L) < -window u (s+(L:ℤ)) L := by
    linarith
  obtain ⟨j, hj, hrise⟩ := exists_drop (fun t => -window u t L) (s+(L:ℤ)) L hn
  have hd := window_step u (s+(i:ℤ)) L
  have hu' := window_step u (s+(L:ℤ)+(j:ℤ)) L
  have hs : u (s+(i:ℤ)+(L:ℤ)) < u (s+(i:ℤ)) := by linarith
  have ht : u (s+(L:ℤ)+(j:ℤ)) < u (s+(L:ℤ)+(j:ℤ)+(L:ℤ)) := by
    linarith
  exact no_reversed_window_signs u hu _ _ (L:ℤ) (by omega) (by omega) hs ht

#print axioms window_step
#print axioms exists_drop
#print axioms window_valley_not_mode
end PureFlag
```
<!-- END LEAN MODULE Windows -->

<!-- BEGIN LEAN MODULE ZeroExtension SHA256 fbce3a90df7c2f68f2d7b8bf61c73f6d2cc1e35b900edb608c3a4fdd4a979d8c -->
```lean
import FTransport
import Windows
namespace PureFlag
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def zeroF (K : FiniteComplex V) (d : ℕ) (i : ℤ) : ℚ :=
  if 0 ≤ i ∧ i < (d : ℤ) then (K.f i.toNat : ℚ) else 0

omit [DecidableEq V] in
theorem finite_unimodal_zeroF (K : FiniteComplex V) (d : ℕ)
    (h : K.Unimodal d) : HasMode (zeroF K d) := by
  obtain ⟨m,hm,inc,dec⟩ := h
  refine ⟨(m : ℤ),?_,?_⟩
  · intro i j hij hjm
    by_cases hi : 0 ≤ i
    · have hj : 0 ≤ j := by omega
      have hid : i < (d : ℤ) := by omega
      have hjd : j < (d : ℤ) := by omega
      simp only [zeroF,hi,hid,hj,hjd,and_self,ite_true]
      exact_mod_cast inc i.toNat j.toNat (by omega) (by omega)
    · have hz : zeroF K d i = 0 := by simp [zeroF,hi]
      rw [hz]
      unfold zeroF
      split_ifs <;> positivity
  · intro i j hmi hij
    have hi : 0 ≤ i := by omega
    have hj : 0 ≤ j := by omega
    by_cases hjd : j < (d : ℤ)
    · have hid : i < (d : ℤ) := by omega
      simp only [zeroF,hi,hid,hj,hjd,and_self,ite_true]
      exact_mod_cast dec i.toNat j.toNat (by omega) (by omega) (by omega)
    · have hz : zeroF K d j = 0 := by simp [zeroF,hjd]
      rw [hz]
      unfold zeroF
      split_ifs <;> positivity

omit [DecidableEq V] in
theorem finite_window_valley (K : FiniteComplex V) (d L : ℕ) (s : ℤ)
    (hl : window (zeroF K d) (s+(L:ℤ)) L < window (zeroF K d) s L)
    (hr : window (zeroF K d) (s+(L:ℤ)) L < window (zeroF K d) (s+(L:ℤ)+(L:ℤ)) L) :
    ¬ K.Unimodal d := by
  intro h
  exact window_valley_not_mode _ _ _ hl hr (finite_unimodal_zeroF K d h)

#print axioms zeroF
#print axioms finite_unimodal_zeroF
#print axioms finite_window_valley
omit [DecidableEq V] in
theorem positive_index_translation
    (K : FiniteComplex V) (d : ℕ) (j : ℤ) (hj : 1 ≤ j) (hd : j ≤ d) :
    zeroF K d (j-1) = (K.f (j.toNat-1) : ℚ) := by
  have h0 : 0 ≤ j-1 := by omega
  have hlt : j-1 < (d:ℤ) := by omega
  simp only [zeroF,h0,hlt,and_self,ite_true]
  have he : (j-1).toNat = j.toNat-1 := by omega
  rw [he]


#print axioms positive_index_translation
end PureFlag
```
<!-- END LEAN MODULE ZeroExtension -->

<!-- BEGIN LEAN MODULE FinalWitness SHA256 572bbd638888589c1c283273fce69fb642e2f93eec68769935633e58e2963949 -->
```lean
import ActualBlocks
import ZeroExtension
import Mathlib.Algebra.BigOperators.Field
namespace PureFlag
open scoped BigOperators
open Polynomial

theorem actualRat_f (a j : ℕ) (hj : 1 ≤ j) :
    (actualRat a).coeff j = ((graphComplex a).f (j-1) : ℚ) := by
  unfold actualRat
  rw [coeff_map]
  change ((facePoly (@Adj a)).coeff j : ℚ) = _
  have hh := actual_f_coeff a (j-1)
  rw [show j-1+1=j by omega] at hh
  exact_mod_cast hh.symm

theorem block_window (a s : ℕ) (ha : a=30000) (hs : 1 ≤ s) (he : s+1250 ≤ 270001) :
    blockMass a s = window (zeroF (graphComplex a) (9*a)) ((s:ℤ)-1) 1250 / commonMass a := by
  classical
  unfold blockMass window
  rw [Finset.sum_div]
  symm
  apply Finset.sum_bij (fun i _ => s+i)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [B,Finset.mem_Ico]
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    simp only [B,Finset.mem_Ico] at hj
    exact ⟨j-s,Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    have hj : 1 ≤ s+i := by omega
    have hd : s+i ≤ 9*a := by omega
    change zeroF (graphComplex a) (9*a) ((s:ℤ)-1+(i:ℤ)) / commonMass a = actualW a (s+i)
    rw [show (s:ℤ)-1+(i:ℤ) = ((s+i:ℕ):ℤ)-1 by omega,
      positive_index_translation _ _ _ (by omega) (by exact_mod_cast hd)]
    simp only [Int.toNat_natCast]
    rw [actualW,actualRat_f a (s+i) hj]

theorem actual_f_not_unimodal (a : ℕ) (ha : a=30000) :
    ¬ (graphComplex a).Unimodal (9*a) := by
  have h := actual_block_valley a ha
  rw [block_window a 145625 ha (by norm_num) (by norm_num),
    block_window a 144375 ha (by norm_num) (by norm_num),
    block_window a 146875 ha (by norm_num) (by norm_num)] at h
  have hl := (div_lt_div_iff_of_pos_right (commonMass_pos a)).mp h.1
  have hr := (div_lt_div_iff_of_pos_right (commonMass_pos a)).mp h.2
  apply finite_window_valley (graphComplex a) (9*a) 1250 144374
  · exact hl
  · exact hr

theorem literal_broad_refutation : ¬ allTypesBroadConjecture :=
  outer_negation_of_actual_failure (actual_f_not_unimodal 30000 rfl)

theorem actual_missing_witness : MissingWitness :=
  ⟨witness_pure,actual_f_not_unimodal 30000 rfl⟩

#print axioms actualRat_f
#print axioms block_window
#print axioms actual_f_not_unimodal
#print axioms literal_broad_refutation
#print axioms actual_missing_witness
end PureFlag
```
<!-- END LEAN MODULE FinalWitness -->

<!-- BEGIN LEAN MODULE AuditV3 SHA256 48ab9663b56d76bea604191f3e10c1256e02941a3cf626411bd1b037321e1ac2 -->
```lean
import FinalWitness
#print axioms PureFlag.independent_flag
#print axioms PureFlag.actual_vertex
#print axioms PureFlag.vertices_card
#print axioms PureFlag.graph_facet_card
#print axioms PureFlag.graph_pure
#print axioms PureFlag.disjointFaceEquiv
#print axioms PureFlag.joinFaceEquiv
#print axioms PureFlag.facePoly_coeff_count
#print axioms PureFlag.actual_graph_polynomial
#print axioms PureFlag.actual_f_coeff
#print axioms PureFlag.actual_face_bound
#print axioms PureFlag.actual_coeff_nonneg
#print axioms PureFlag.actual_coeff_support
#print axioms PureFlag.first_branch_moments
#print axioms PureFlag.second_branch_moments
#print axioms PureFlag.first_coefficients
#print axioms PureFlag.second_coefficients
#print axioms PureFlag.first_scale
#print axioms PureFlag.second_scale
#print axioms PureFlag.actual_normalization
#print axioms PureFlag.actual_first_branch_mass
#print axioms PureFlag.actual_second_branch_mass
#print axioms PureFlag.actualW_nonneg
#print axioms PureFlag.actualW_support
#print axioms PureFlag.actualW_total
#print axioms PureFlag.first_range
#print axioms PureFlag.second_range
#print axioms PureFlag.left_concentration
#print axioms PureFlag.right_concentration
#print axioms PureFlag.middle_bound
#print axioms PureFlag.actual_block_valley
#print axioms PureFlag.block_window
#print axioms PureFlag.actual_f_not_unimodal
#print axioms PureFlag.actual_missing_witness
#print axioms PureFlag.literal_broad_refutation
```
<!-- END LEAN MODULE AuditV3 -->

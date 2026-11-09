import ChordComb4Subdiagram
import Mathlib.Data.Fintype.Prod
namespace Chord.Comb4

theorem crosses_symm {n} {D : Diagram n} {a b} (h : Crosses D a b) :
    Crosses D b a := ⟨h.2.1,h.1,h.2.2.symm⟩

theorem crosses_irrefl {n} (D : Diagram n) (a) : ¬Crosses D a a := by
  rintro ⟨_,_,h | h⟩ <;> exact (lt_irrefl a) h.1

/-- Select both endpoints of each of k distinct chords, represented by their
lower endpoints. This formulation includes all choices of retained chords. -/
def selectedEndpoint {n k} (D : Diagram n) (a : Fin k → Fin (2*n))
    (x : Fin k × Bool) : Fin (2*n) := if x.2 then D.partner (a x.1) else a x.1

theorem selectedEndpoint_injective {n k} (D : Diagram n) (a : Fin k → Fin (2*n))
    (ha : Function.Injective a) (hl : ∀ i, a i < D.partner (a i)) :
    Function.Injective (selectedEndpoint D a) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  cases p <;> cases q
  · simp only [selectedEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    exact Prod.ext (ha h) rfl
  · simp only [selectedEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    have h' := congrArg D.partner h
    rw [D.involutive] at h'
    have hh : D.partner (a j) < a j := by simpa only [h, D.involutive] using hl i
    exact False.elim ((lt_asymm hh) (hl j))
  · simp only [selectedEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    have h' := congrArg D.partner h
    rw [D.involutive] at h'
    have hh : D.partner (a j) < a j := by simpa only [h', D.involutive] using hl i
    exact False.elim ((lt_asymm hh) (hl j))
  · simp only [selectedEndpoint, ↓reduceIte] at h
    have h' := congrArg D.partner h
    simp only [D.involutive] at h'
    exact Prod.ext (ha h') rfl

def selectedSet {n k} (D : Diagram n) (a : Fin k → Fin (2*n)) : Finset (Fin (2*n)) :=
  Finset.univ.image (selectedEndpoint D a)

theorem selected_card {n k} (D : Diagram n) (a : Fin k → Fin (2*n))
    (ha : Function.Injective a) (hl : ∀ i, a i < D.partner (a i)) :
    (selectedSet D a).card = 2*k := by
  rw [selectedSet, Finset.card_image_of_injective _ (selectedEndpoint_injective D a ha hl)]
  simp [Nat.mul_comm]

theorem selected_closed {n k} (D : Diagram n) (a : Fin k → Fin (2*n)) :
    ∀ i ∈ selectedSet D a, D.partner i ∈ selectedSet D a := by
  intro i hi
  obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hi
  cases b
  · exact Finset.mem_image.mpr ⟨(j,true), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(j,false), Finset.mem_univ _, D.involutive (a j) |>.symm⟩

/-- The retained lower endpoints are exactly the chosen representatives. -/
theorem selected_lower {n k} (D : Diagram n) (a : Fin k → Fin (2*n))
    (hl : ∀ i, a i < D.partner (a i)) {b} (hb : b ∈ selectedSet D a)
    (hbl : b < D.partner b) : ∃ i, b = a i := by
  obtain ⟨⟨i,p⟩,_,rfl⟩ := Finset.mem_image.mp hb
  cases p
  · exact ⟨i,rfl⟩
  · change D.partner (a i) < D.partner (D.partner (a i)) at hbl
    rw [D.involutive] at hbl
    exact False.elim ((lt_asymm (hl i)) hbl)

/-- Compression of any five retained chords, without a reindexing hypothesis. -/
def fiveSelection {n} (D : Diagram n) (a : Fin 5 → Fin (2*n))
    (ha : Function.Injective a) (hl : ∀ i, a i < D.partner (a i)) : Diagram 5 :=
  compress D (selectedSet D a) (selected_card D a ha hl) (selected_closed D a)

def fiveSelectionSubdiagram {n} (D : Diagram n) (a : Fin 5 → Fin (2*n))
    (ha : Function.Injective a) (hl : ∀ i, a i < D.partner (a i)) :
    Subdiagram (fiveSelection D a ha hl) D :=
  compression D (selectedSet D a) (selected_card D a ha hl) (selected_closed D a)

/-- The finite lemma excludes any five distinct chords with no isolated vertex.
Edges beyond the supplied witnesses do not matter; inducedness is unnecessary. -/
theorem no_five_selection {n} (D : Diagram n)
    (hf : ∀ A : Diagram 5, Subdiagram A D → FiveProperty A)
    (a : Fin 5 → Fin (2*n)) (ha : Function.Injective a)
    (hl : ∀ i, a i < D.partner (a i))
    (hx : ∀ i, ∃ j, Crosses D (a i) (a j)) : False := by
  apply no_five_without_isolated D hf (selectedSet D a)
    (selected_card D a ha hl) (selected_closed D a)
  intro b hb hbl
  obtain ⟨i,rfl⟩ := selected_lower D a hl hb hbl
  obtain ⟨j,hj⟩ := hx i
  exact ⟨a j, Finset.mem_image.mpr ⟨(j,false), Finset.mem_univ _, rfl⟩, hj⟩

/-- In particular, five vertices along any simple path are impossible. -/
theorem no_five_path {n} (D : Diagram n)
    (hf : ∀ A : Diagram 5, Subdiagram A D → FiveProperty A)
    (a : Fin 5 → Fin (2*n)) (ha : Function.Injective a)
    (hl : ∀ i, a i < D.partner (a i))
    (h01 : Crosses D (a 0) (a 1)) (h12 : Crosses D (a 1) (a 2))
    (h23 : Crosses D (a 2) (a 3)) (h34 : Crosses D (a 3) (a 4)) : False := by
  apply no_five_selection D hf a ha hl
  intro i
  match i with
  | ⟨0,_⟩ => exact ⟨1,h01⟩
  | ⟨1,_⟩ => exact ⟨2,h12⟩
  | ⟨2,_⟩ => exact ⟨3,h23⟩
  | ⟨3,_⟩ => exact ⟨4,h34⟩
  | ⟨4,_⟩ => exact ⟨3,crosses_symm h34⟩
end Chord.Comb4

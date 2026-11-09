import ChordComb2Final
import Mathlib.Data.Finset.Sort
namespace Chord.Comb4

/-- Increasing compression of any pairing-closed endpoint set. -/
def compress {n k} (D : Diagram n) (s : Finset (Fin (2*n)))
    (hs : s.card = 2*k) (closed : ∀ i ∈ s, D.partner i ∈ s) : Diagram k where
  partner i := (s.orderIsoOfFin hs).symm
    ⟨D.partner (s.orderIsoOfFin hs i), closed _ (s.orderIsoOfFin hs i).property⟩
  involutive i := by
    apply (s.orderIsoOfFin hs).injective
    apply Subtype.ext
    simp [D.involutive]
  noFixed i h := by
    have hh := congrArg (fun j => ((s.orderIsoOfFin hs j).val)) h
    rw [OrderIso.apply_symm_apply] at hh
    exact D.noFixed _ hh

/-- Compression supplies exactly the frozen order-preserving Subdiagram structure. -/
def compression {n k} (D : Diagram n) (s : Finset (Fin (2*n)))
    (hs : s.card = 2*k) (closed : ∀ i ∈ s, D.partner i ∈ s) :
    Subdiagram (compress D s hs closed) D where
  positions := s.orderEmbOfFin hs
  increasing := (s.orderEmbOfFin hs).strictMono
  closed i := by
    change D.partner (s.orderIsoOfFin hs i).val =
      ((s.orderIsoOfFin hs) ((s.orderIsoOfFin hs).symm _)).val
    simp

/-- Crossing is preserved and reflected by every literal Subdiagram. -/
theorem crosses_iff {k n} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) (a b : Fin (2*k)) :
    Crosses D (S.positions a) (S.positions b) ↔ Crosses A a b := by
  unfold Crosses
  rw [S.closed, S.closed]
  simp only [S.increasing.lt_iff_lt]

theorem triangle_transport {k n} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) (h : HasTriangle A) : HasTriangle D := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := h
  exact ⟨S.positions a, S.positions b, S.positions c,
    (crosses_iff S a b).mpr hab, (crosses_iff S a c).mpr hac,
    (crosses_iff S b c).mpr hbc⟩

def identitySubdiagram {n} (D : Diagram n) : Subdiagram D D where
  positions := id
  increasing := fun _ _ h => h
  closed _ := rfl

def composeSubdiagram {k m n} {A : Diagram k} {B : Diagram m} {D : Diagram n}
    (S : Subdiagram A B) (T : Subdiagram B D) : Subdiagram A D where
  positions := T.positions ∘ S.positions
  increasing := T.increasing.comp S.increasing
  closed i := by simp only [Function.comp_apply, T.closed, S.closed]

/-- The five-chord case of large rigidity follows from the actual FiveProperty. -/
theorem rigidity_five (D : Diagram 5) (ht : HasTriangle D)
    (hf : ∀ A : Diagram 5, Subdiagram A D → FiveProperty A) :
    Equivalent D (r3Block 5 (by decide)) :=
  (hf D (identitySubdiagram D)).2 ht

/-- An endpoint set with no isolated retained chord contradicts FiveProperty. -/
theorem no_five_without_isolated {n} (D : Diagram n)
    (hf : ∀ A : Diagram 5, Subdiagram A D → FiveProperty A)
    (s : Finset (Fin (2*n))) (hs : s.card = 10)
    (hc : ∀ i ∈ s, D.partner i ∈ s)
    (hx : ∀ a ∈ s, a < D.partner a →
      ∃ b ∈ s, Crosses D a b) : False := by
  let A := compress (k := 5) D s hs hc
  let S := compression (k := 5) D s hs hc
  obtain ⟨a,ha,hi⟩ := (hf A S).1
  have hap : S.positions a ∈ s := Finset.orderEmbOfFin_mem s hs a
  have hal : S.positions a < D.partner (S.positions a) := by
    rw [S.closed]
    exact S.increasing ha
  obtain ⟨b,hb,hab⟩ := hx _ hap hal
  let j := (s.orderIsoOfFin hs).symm ⟨b,hb⟩
  have hj : S.positions j = b := by
    change ((s.orderIsoOfFin hs) ((s.orderIsoOfFin hs).symm ⟨b,hb⟩)).val = b
    simp
  have hcross : Crosses A a j := (crosses_iff S a j).mp (hj.symm ▸ hab)
  exact (hi j).1 hcross
end Chord.Comb4

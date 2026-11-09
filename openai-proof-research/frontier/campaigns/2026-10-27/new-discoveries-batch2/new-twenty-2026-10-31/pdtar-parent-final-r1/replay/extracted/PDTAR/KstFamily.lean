import PDTAR.FortDuality
namespace PDTAR
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Ordered partition; exchanging the parts gives the mirror version. -/
def Parts (A B : Finset V) : Prop := Disjoint A B ∧ A ∪ B = univ

def CompleteBetween (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Parts A B ∧ ∀ x y, G.Adj x y ↔ (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)

theorem Parts.mem_or {A B : Finset V} (h : Parts A B) (x : V) : x ∈ A ∨ x ∈ B := by
  have hx : x ∈ A ∪ B := h.2 ▸ mem_univ x
  exact mem_union.mp hx

theorem Parts.not_both {A B : Finset V} (h : Parts A B) {x : V} :
    x ∈ A → x ∈ B → False := fun ha hb => disjoint_left.mp h.1 ha hb

theorem completeBetween_swap {G : SimpleGraph V} {A B : Finset V}
    (h : CompleteBetween G A B) : CompleteBetween G B A := by
  refine ⟨⟨h.1.1.symm, by simpa [union_comm] using h.1.2⟩, ?_⟩
  intro x y
  rw [h.2]
  exact or_comm

theorem mixed_pair_isPD {G : SimpleGraph V} {A B : Finset V}
    (h : CompleteBetween G A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    IsPD G {a,b} := by
  refine ⟨1, eq_univ_of_forall fun x => ?_⟩
  change x ∈ closed G {a,b}
  rcases h.1.mem_or x with hx | hx
  · exact (mem_closed G _ _).mpr (.inr ⟨b,by simp,(h.2 b x).mpr (.inr ⟨hb,hx⟩)⟩)
  · exact (mem_closed G _ _).mpr (.inr ⟨a,by simp,(h.2 a x).mpr (.inl ⟨ha,hx⟩)⟩)

theorem erase_part_isPD {G : SimpleGraph V} {A B : Finset V}
    (h : CompleteBetween G A B) {x : V} (hx : x ∈ A)
    (ha : (A.erase x).Nonempty) (hb : B.Nonempty) : IsPD G (A.erase x) := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  have hB : ∀ u ∈ B, u ∈ closed G (A.erase x) := by
    intro u hu
    exact (mem_closed G _ _).mpr (.inr ⟨a,ha,(h.2 a u).mpr (.inl ⟨mem_of_mem_erase ha,hu⟩)⟩)
  have hrest : ∀ u, u ≠ x → u ∈ closed G (A.erase x) := by
    intro u hne
    rcases h.1.mem_or u with hu | hu
    · exact subset_closed G _ (mem_erase.mpr ⟨hne,hu⟩)
    · exact hB u hu
  refine ⟨2, eq_univ_of_forall fun u => ?_⟩
  change u ∈ step G (closed G (A.erase x))
  by_cases he : u = x
  · subst u
    apply (mem_step G _ _).mpr
    right
    exact ⟨b,hB b hb,(h.2 b x).mpr (.inr ⟨hb,hx⟩),fun w _ hn =>
      by_contra fun hne => hn (hrest w hne)⟩
  · exact subset_step G _ (hrest u he)

theorem pair_isFort {G : SimpleGraph V} {A B : Finset V}
    (h : CompleteBetween G A B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hne : x ≠ y) : IsFort G {x,y} := by
  classical
  refine ⟨by simp, ?_⟩
  intro v _ u hu ha
  have huA : u ∈ A := by rcases mem_insert.mp hu with rfl | hu; exact hx; exact (mem_singleton.mp hu) ▸ hy
  have hvB : v ∈ B := by
    rcases (h.2 v u).mp ha with ⟨_,huB⟩ | ⟨hvB,_⟩
    · exact False.elim (h.1.not_both huA huB)
    · exact hvB
  by_cases he : u = x
  · exact ⟨y,by simp,by simpa [he] using Ne.symm hne,(h.2 v y).mpr (.inr ⟨hvB,hy⟩)⟩
  · exact ⟨x,by simp,Ne.symm he,(h.2 v x).mpr (.inr ⟨hvB,hx⟩)⟩

theorem erase_pair_not_isPD {G : SimpleGraph V} {A B : Finset V}
    (h : CompleteBetween G A B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hne : x ≠ y) : ¬ IsPD G (A \ {x,y}) := by
  intro hp
  obtain ⟨u,hu⟩ := (fort_duality G _).mp hp {x,y} (pair_isFort h hx hy hne)
  obtain ⟨hup,huc⟩ := mem_inter.mp hu
  have huA : u ∈ A := by rcases mem_insert.mp hup with rfl | hh; exact hx; exact (mem_singleton.mp hh) ▸ hy
  rcases (mem_closed G _ _).mp huc with hs | ⟨v,hv,ha⟩
  · exact (mem_sdiff.mp hs).2 hup
  · have hvA := (mem_sdiff.mp hv).1
    rcases (h.2 v u).mp ha with ⟨_,huB⟩ | ⟨hvB,_⟩
    · exact h.1.not_both huA huB
    · exact h.1.not_both hvA hvB
end PDTAR

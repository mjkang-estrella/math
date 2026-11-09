import G1
import Mathlib.Data.Finset.Insert

namespace Bicir
open Relation

variable {g : Gr}

/-- The union of the two endpoint-components of `e` (computed in `F`). -/
noncomputable def uu (g : Gr) (F : Finset (Fin g.m)) (e : Fin g.m) : Finset (Fin g.v) :=
  cmp g F (g.ep e).1 ∪ cmp g F (g.ep e).2

theorem cmp_mem_trans {g : Gr} {F : Finset (Fin g.m)} {x z t : Fin g.v}
    (h : ReflTransGen (Adj g F) x z) (hz : z ∈ cmp g F t) : x ∈ cmp g F t := by
  rw [mem_cmp] at hz ⊢
  exact ReflTransGen.trans hz (rtg_symm h)

theorem uu_mem_trans {g : Gr} {F : Finset (Fin g.m)} {x z : Fin g.v} {e : Fin g.m}
    (h : ReflTransGen (Adj g F) x z) (hz : z ∈ uu g F e) : x ∈ uu g F e := by
  have hz' : z ∈ cmp g F (g.ep e).1 ∨ z ∈ cmp g F (g.ep e).2 :=
    Finset.mem_union.mp (show z ∈ cmp g F (g.ep e).1 ∪ cmp g F (g.ep e).2 from hz)
  rcases hz' with hz1 | hz2
  · have hx : x ∈ cmp g F (g.ep e).1 ∪ cmp g F (g.ep e).2 :=
      Finset.mem_union.mpr (Or.inl (cmp_mem_trans h hz1))
    exact hx
  · have hx : x ∈ cmp g F (g.ep e).1 ∪ cmp g F (g.ep e).2 :=
      Finset.mem_union.mpr (Or.inr (cmp_mem_trans h hz2))
    exact hx

theorem endsInU {g : Gr} {F : Finset (Fin g.m)} {e : Fin g.m} {z y : Fin g.v}
    (h : ((g.ep e).1 = z ∧ (g.ep e).2 = y) ∨ ((g.ep e).1 = y ∧ (g.ep e).2 = z)) :
    z ∈ uu g F e ∧ y ∈ uu g F e := by
  have key : ∀ a : Fin g.v, ((g.ep e).1 = a ∨ (g.ep e).2 = a) → a ∈ uu g F e := by
    intro a ha
    rcases ha with ha | ha
    · exact Finset.mem_union_left _ (mem_cmp.mpr (by rw [ha]))
    · exact Finset.mem_union_right _ (mem_cmp.mpr (by rw [ha]))
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨key _ (Or.inl h1), key _ (Or.inr h2)⟩
  · exact ⟨key _ (Or.inr h2), key _ (Or.inl h1)⟩

theorem stepAdj {g : Gr} {F : Finset (Fin g.m)} {w : Fin g.m} {z y : Fin g.v}
    (hw : w ∈ F)
    (h : ((g.ep w).1 = z ∧ (g.ep w).2 = y) ∨ ((g.ep w).1 = y ∧ (g.ep w).2 = z)) :
    ReflTransGen (Adj g F) z y :=
  ReflTransGen.single ⟨w, hw, h⟩

theorem mergeAux (g : Gr) (F : Finset (Fin g.m)) (e : Fin g.m) (x z y : Fin g.v)
    (ih : ReflTransGen (Adj g F) x z ∨ (x ∈ uu g F e ∧ z ∈ uu g F e))
    (w : Fin g.m) (hw : w ∈ insert e F)
    (hzy : ((g.ep w).1 = z ∧ (g.ep w).2 = y) ∨ ((g.ep w).1 = y ∧ (g.ep w).2 = z)) :
    ReflTransGen (Adj g F) x y ∨ (x ∈ uu g F e ∧ y ∈ uu g F e) := by
  rcases ih with ih | ⟨hxU, hzU⟩
  · rcases Finset.mem_insert.mp hw with hwE | hwF
    · rw [hwE] at hzy
      obtain ⟨hzU', hyU⟩ := endsInU hzy
      exact Or.inr ⟨uu_mem_trans ih hzU', hyU⟩
    · exact Or.inl (ReflTransGen.trans ih (stepAdj hwF hzy))
  · rcases Finset.mem_insert.mp hw with hwE | hwF
    · rw [hwE] at hzy
      exact Or.inr ⟨hxU, (endsInU hzy).2⟩
    · exact Or.inr ⟨hxU, uu_mem_trans (rtg_symm (stepAdj hwF hzy)) hzU⟩

theorem merge_rtg (g : Gr) (F : Finset (Fin g.m)) (e : Fin g.m) :
    ∀ x y : Fin g.v, ReflTransGen (Adj g (insert e F)) x y →
      ReflTransGen (Adj g F) x y ∨ (x ∈ uu g F e ∧ y ∈ uu g F e) := by
  intro x y h
  induction h with
  | refl => exact Or.inl ReflTransGen.refl
  | tail _h1 hstep ih =>
    obtain ⟨w, hw, hzy⟩ := hstep
    exact mergeAux g F e x _ _ ih w hw hzy

theorem cmp_ins_sub (g : Gr) (F : Finset (Fin g.m)) (e : Fin g.m) (x y : Fin g.v)
    (h : y ∈ cmp g (insert e F) x) :
    y ∈ cmp g F x ∨ (x ∈ uu g F e ∧ y ∈ uu g F e) := by
  rw [mem_cmp] at h
  rcases merge_rtg g F e x y h with h' | hu
  · exact Or.inl (mem_cmp.mpr h')
  · exact Or.inr hu

end Bicir

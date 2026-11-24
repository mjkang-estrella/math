# Lean source appendix

Status: COMPLETE. All modules in dependency order, byte exact. Fresh extraction, compilation and kernel replay passed.

### `RFBGraph.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

set_option linter.unusedSimpArgs false

namespace RFB

abbrev Vertex (r s : ℕ) := Fin r × Option (Fin s × Fin 3)
abbrev Edge (r s : ℕ) := Fin r × Fin s × Fin 5

def FBAdj (s : ℕ) : Option (Fin s × Fin 3) → Option (Fin s × Fin 3) → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some (i,a), some (j,b) => i = j ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)

instance (s : ℕ) : DecidableRel (FBAdj s) := fun a b => by
  cases a <;> cases b <;> simp only [FBAdj] <;> infer_instance

def rFB (r s : ℕ) : SimpleGraph (Vertex r s) where
  Adj p q := p.1 = q.1 ∧ FBAdj s p.2 q.2
  symm := ⟨by
    rintro ⟨i,a⟩ ⟨j,b⟩ ⟨h,h'⟩
    refine ⟨h.symm, ?_⟩
    cases a <;> cases b <;> simp_all [FBAdj, eq_comm, or_comm]⟩
  loopless := ⟨by
    rintro ⟨i,a⟩ ⟨_,h⟩
    cases a with
    | none => exact h
    | some p => simp only [FBAdj] at h; omega⟩

instance (r s : ℕ) : DecidableRel (rFB r s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def ends {r s : ℕ} (e : Edge r s) : Vertex r s × Vertex r s :=
  let h : Vertex r s := (e.1, none)
  let u : Vertex r s := (e.1, some (e.2.1, 0))
  let w : Vertex r s := (e.1, some (e.2.1, 1))
  let v : Vertex r s := (e.1, some (e.2.1, 2))
  match e.2.2.val with
  | 0 => (h,u)
  | 1 => (u,w)
  | 2 => (h,w)
  | 3 => (w,v)
  | _ => (v,h)

def edgeMap {r s : ℕ} (e : Edge r s) : (rFB r s).edgeSet :=
  ⟨s((ends e).1, (ends e).2), by
    rcases e with ⟨i,j,t⟩
    fin_cases t <;> simp [ends, SimpleGraph.mem_edgeSet, rFB, FBAdj]⟩

theorem edgeMap_injective (r s : ℕ) : Function.Injective (@edgeMap r s) := by
  rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
  have h' := congrArg Subtype.val h
  fin_cases t <;> fin_cases t' <;>
    simp [edgeMap, ends, Sym2.eq_iff] at h' <;> simp_all

theorem edgeMap_surjective (r s : ℕ) : Function.Surjective (@edgeMap r s) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | _ a b =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    change i = j ∧ FBAdj s a b at he
    rcases he with ⟨rfl,he⟩
    cases a with
    | none =>
      cases b with
      | none => exact False.elim he
      | some p =>
        rcases p with ⟨l,t⟩
        fin_cases t
        · exact ⟨(i,l,0), Subtype.ext rfl⟩
        · exact ⟨(i,l,2), Subtype.ext rfl⟩
        · exact ⟨(i,l,4), Subtype.ext (Sym2.eq_swap)⟩
    | some p =>
      rcases p with ⟨l,t⟩
      cases b with
      | none =>
        fin_cases t
        · exact ⟨(i,l,0), Subtype.ext (Sym2.eq_swap)⟩
        · exact ⟨(i,l,2), Subtype.ext (Sym2.eq_swap)⟩
        · exact ⟨(i,l,4), Subtype.ext rfl⟩
      | some q =>
        rcases q with ⟨l',t'⟩
        change l = l' ∧ _ at he
        rcases he with ⟨rfl,he⟩
        fin_cases t <;> fin_cases t' <;> simp only [Fin.val_zero, Fin.val_one,
          Fin.val_two] at he
        all_goals first
          | omega
          | exact ⟨(i,l,1), Subtype.ext rfl⟩
          | exact ⟨(i,l,1), Subtype.ext (Sym2.eq_swap)⟩
          | exact ⟨(i,l,3), Subtype.ext rfl⟩
          | exact ⟨(i,l,3), Subtype.ext (Sym2.eq_swap)⟩

noncomputable def edgeEquiv (r s : ℕ) : Edge r s ≃ (rFB r s).edgeSet :=
  Equiv.ofBijective edgeMap ⟨edgeMap_injective r s, edgeMap_surjective r s⟩

@[simp] theorem edgeEquiv_apply {r s : ℕ} (e : Edge r s) :
    edgeEquiv r s e = edgeMap e := rfl

theorem card_vertices (r s : ℕ) : Fintype.card (Vertex r s) = r * (1 + 3*s) := by
  simp [Fintype.card_prod, Fintype.card_option, Nat.mul_comm, Nat.add_comm]

theorem card_edges (r s : ℕ) : Fintype.card (rFB r s).edgeSet = 5*r*s := by
  rw [← Fintype.card_congr (edgeEquiv r s)]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

section LocalAntimagic
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

def vsum (f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (v : V) : ℕ :=
  ∑ e ∈ (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))), ((f e : ℕ) + 1)

def IsLocalAntimagic (f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) : Prop :=
  ∀ u v, G.Adj u v → vsum G f u ≠ vsum G f v

def colorCount (f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) : ℕ :=
  (Finset.univ.image (vsum G f)).card

noncomputable def chiLA : ℕ :=
  sInf {c | ∃ f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet),
    IsLocalAntimagic G f ∧ colorCount G f = c}
end LocalAntimagic

#print axioms edgeMap_injective
#print axioms edgeMap_surjective
#print axioms card_vertices
#print axioms card_edges
#print chiLA
end RFB
```

### `RFBLabeling.lean`

```lean
import RFBGraph

set_option linter.unusedSimpArgs false
namespace RFB

structure Labeling (r s : ℕ) where
  label : Edge r s → ℕ
  positive : ∀ e, 0 < label e
  bounded : ∀ e, label e ≤ 5*r*s
  injective : Function.Injective label

def indexedSum {r s : ℕ} (label : Edge r s → ℕ) (v : Vertex r s) : ℕ :=
  ∑ e : Edge r s, if v ∈ (edgeMap e : Sym2 (Vertex r s)) then label e else 0

namespace Labeling
variable {r s : ℕ} (L : Labeling r s)

def toFin (e : Edge r s) : Fin (Fintype.card (rFB r s).edgeSet) :=
  ⟨L.label e - 1, by rw [card_edges]; have := L.positive e; have := L.bounded e; omega⟩

theorem toFin_injective : Function.Injective L.toFin := by
  intro e e' h
  apply L.injective
  have := congrArg Fin.val h
  have := L.positive e
  have := L.positive e'
  simp only [toFin] at *
  omega

noncomputable def finEquiv : Edge r s ≃ Fin (Fintype.card (rFB r s).edgeSet) := by
  apply Equiv.ofBijective L.toFin
  apply (Fintype.bijective_iff_injective_and_card L.toFin).mpr
  refine ⟨L.toFin_injective, ?_⟩
  rw [Fintype.card_fin, card_edges]
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp [Nat.mul_comm, Nat.mul_left_comm]

noncomputable def labelEquiv : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet) :=
  (edgeEquiv r s).symm.trans L.finEquiv

@[simp] theorem labelEquiv_edgeMap (e : Edge r s) :
    (L.labelEquiv (edgeMap e)).val + 1 = L.label e := by
  change (L.toFin ((edgeEquiv r s).symm (edgeEquiv r s e))).val + 1 = _
  rw [Equiv.symm_apply_apply]
  have := L.positive e
  simp only [toFin]
  omega

end Labeling

theorem vsum_transfer {r s : ℕ} (L : Labeling r s) (v : Vertex r s) :
    vsum (rFB r s) L.labelEquiv v = indexedSum L.label v := by
  classical
  simp only [vsum, Finset.sum_filter, indexedSum]
  rw [← (edgeEquiv r s).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  simp only [edgeEquiv_apply, Labeling.labelEquiv_edgeMap]

theorem colorCount_transfer {r s : ℕ} (L : Labeling r s) :
    colorCount (rFB r s) L.labelEquiv = (Finset.univ.image (indexedSum L.label)).card := by
  unfold colorCount
  congr 2
  funext v
  exact vsum_transfer L v

theorem proper_transfer {r s : ℕ} (L : Labeling r s)
    (h : ∀ u v, (rFB r s).Adj u v → indexedSum L.label u ≠ indexedSum L.label v) :
    IsLocalAntimagic (rFB r s) L.labelEquiv := by
  intro u v huv
  simpa only [vsum_transfer] using h u v huv

theorem triangle_lower (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (f : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet))
    (hf : IsLocalAntimagic (rFB r s) f) : 3 ≤ colorCount (rFB r s) f := by
  let i : Fin r := ⟨0,hr⟩
  let j : Fin s := ⟨0,hs⟩
  let h : Vertex r s := (i,none)
  let u : Vertex r s := (i,some (j,0))
  let w : Vertex r s := (i,some (j,1))
  have hhu : (rFB r s).Adj h u := by simp [h,u,rFB,FBAdj]
  have hhw : (rFB r s).Adj h w := by simp [h,w,rFB,FBAdj]
  have huw : (rFB r s).Adj u w := by simp [u,w,rFB,FBAdj]
  have hn1 := hf h u hhu
  have hn2 := hf h w hhw
  have hn3 := hf u w huw
  let S : Finset ℕ := {vsum (rFB r s) f h, vsum (rFB r s) f u, vsum (rFB r s) f w}
  have hc : S.card = 3 := by simp [S, hn1, hn2, hn3]
  have hsub : S ⊆ Finset.univ.image (vsum (rFB r s) f) := by
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  exact hc.symm.trans_le (Finset.card_le_card hsub)

theorem chiLA_of_witness (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (f : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet))
    (hf : IsLocalAntimagic (rFB r s) f) (hc : colorCount (rFB r s) f = 3) :
    chiLA (rFB r s) = 3 := by
  let S : Set ℕ := {c | ∃ f : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet),
    IsLocalAntimagic (rFB r s) f ∧ colorCount (rFB r s) f = c}
  have h3 : 3 ∈ S := ⟨f,hf,hc⟩
  have hne : S.Nonempty := ⟨3,h3⟩
  change sInf S = 3
  apply Nat.le_antisymm (Nat.sInf_le h3)
  obtain ⟨g,hg,hgc⟩ := Nat.sInf_mem hne
  rw [← hgc]
  exact triangle_lower r s hr hs g hg

#print axioms vsum_transfer
#print axioms triangle_lower
#print axioms chiLA_of_witness
end RFB
```

### `RFBSmallest.lean`

```lean
import RFBLabeling
import Mathlib.Data.Fin.VecNotation

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace RFB

def smallestLabels : Edge 2 3 → ℕ := fun e =>
  (![
    ![![29,2,27,1,30], ![17,14,13,3,28], ![18,12,9,10,20]],
    ![![22,8,16,7,23], ![19,11,15,5,25], ![24,6,21,4,26]]
  ] : Fin 2 → Fin 3 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def smallestLabeling : Labeling 2 3 where
  label := smallestLabels
  positive := by decide
  bounded := by decide
  injective := by decide

theorem smallest_proper : ∀ u v, (rFB 2 3).Adj u v →
    indexedSum smallestLabels u ≠ indexedSum smallestLabels v := by decide

theorem smallest_three :
    (Finset.univ.image (indexedSum smallestLabels)).card = 3 := by decide

theorem smallest_case : chiLA (rFB 2 3) = 3 := by
  apply chiLA_of_witness 2 3 (by decide) (by decide) smallestLabeling.labelEquiv
  · exact proper_transfer smallestLabeling smallest_proper
  · rw [colorCount_transfer]
    exact smallest_three

theorem smallest_vertices : Fintype.card (Vertex 2 3) = 20 := by decide

theorem smallest_edges : Fintype.card (rFB 2 3).edgeSet = 30 := by
  rw [card_edges]

#print axioms smallest_case
#print axioms smallest_vertices
#print axioms smallest_edges
end RFB
```

### `RFBSupply.lean`

```lean
import RFBGraph

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace RFB

/-- The source array, with 1-based column i and edge order xu,uw,xw,wv,xv. -/
def supply (k i : ℕ) (t : Fin 5) : ℕ :=
  match t.val with
  | 0 => if i = 1 then 10*k else if i ≤ k then 9*k+2-i
      else if i < 2*k then 11*k-i else 8*k+1
  | 1 => if i = 1 then 1 else if i ≤ k then k+i-1
      else if i < 2*k then i-k+1 else 2*k
  | 2 => if i = 1 then 7*k else if i ≤ k then 6*k+3-2*i
      else if i < 2*k then 8*k-2*i else 3*k+1
  | 3 => if i = 1 then 6*k else if i ≤ k then 6*k+i-1
      else if i < 2*k then 6*k+i else 8*k
  | _ => if i = 1 then 4*k+1 else if i ≤ k then 4*k+2-i
      else if i < 2*k then 4*k+1-i else 2*k+1

theorem supply_bounds (k i : ℕ) (hk : 11 ≤ k) (hi : 1 ≤ i) (hi' : i ≤ 2*k)
    (t : Fin 5) : 0 < supply k i t ∧ supply k i t ≤ 10*k := by
  fin_cases t <;> simp only [supply] <;> split_ifs <;> omega

theorem supply_injective_aux (k i j : ℕ) (hk : 11 ≤ k)
    (hi : 1 ≤ i) (hi' : i ≤ 2*k) (hj : 1 ≤ j) (hj' : j ≤ 2*k)
    (t u : Fin 5) (h : supply k i t = supply k j u) : i = j ∧ t = u := by
  fin_cases t <;> fin_cases u <;> simp only [supply] at h <;>
    split_ifs at h <;> (constructor <;> omega)

def supplyLabel (k : ℕ) (hk : 11 ≤ k) (e : Fin (2*k) × Fin 5) : Fin (10*k) :=
  ⟨supply k (e.1.val+1) e.2 - 1, by
    have := supply_bounds k (e.1.val+1) hk (by omega) (by have := e.1.isLt; omega) e.2
    omega⟩

theorem supply_bijective (k : ℕ) (hk : 11 ≤ k) :
    Function.Bijective (supplyLabel k hk) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨i,t⟩ ⟨j,u⟩ he
    have h := congrArg Fin.val he
    have hi := supply_bounds k (i.val+1) hk (by omega) (by have := i.isLt; omega) t
    have hj := supply_bounds k (j.val+1) hk (by omega) (by have := j.isLt; omega) u
    simp only [supplyLabel, Prod.fst, Prod.snd] at h
    have heq : supply k (i.val+1) t = supply k (j.val+1) u := by omega
    obtain ⟨hij,htu⟩ := supply_injective_aux k (i.val+1) (j.val+1) hk
      (by omega) (by have := i.isLt; omega) (by omega) (by have := j.isLt; omega) t u heq
    exact congrArg₂ Prod.mk (Fin.ext (Nat.add_right_cancel hij)) htu
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega

/-- Source ordinary-blade equations, with no numerical sampling. -/
theorem supply_ordinary (k i : ℕ) (hk : 11 ≤ k) (hi : 1 ≤ i) (hi' : i ≤ 2*k) :
    supply k i 0 + supply k i 1 = 10*k+1 ∧
    supply k i 3 + supply k i 4 = 10*k+1 ∧
    supply k i 1 + supply k i 2 + supply k i 3 = 13*k+1 := by
  simp [supply]
  split_ifs <;> omega

#print axioms supply_bounds
#print axioms supply_injective_aux
#print axioms supply_bijective
#print axioms supply_ordinary
end RFB
```

### `RFBWeights.lean`

```lean
import RFBLabeling
import Mathlib.Algebra.BigOperators.Fin

set_option linter.unusedSimpArgs false
namespace RFB

theorem indexedSum_hub {r s : ℕ} (L : Edge r s → ℕ) (i : Fin r) :
    indexedSum L (i,none) = ∑ j : Fin s, (L (i,j,0) + L (i,j,2) + L (i,j,4)) := by
  simp [indexedSum, Fintype.sum_prod_type, Fin.sum_univ_succ, edgeMap, ends,
    Sym2.mem_iff, Finset.sum_add_distrib, ite_and, Nat.add_assoc]

theorem indexedSum_u {r s : ℕ} (L : Edge r s → ℕ) (i : Fin r) (j : Fin s) :
    indexedSum L (i,some (j,0)) = L (i,j,0) + L (i,j,1) := by
  simp [indexedSum, Fintype.sum_prod_type, Fin.sum_univ_succ, edgeMap, ends,
    Sym2.mem_iff, Finset.sum_add_distrib, ite_and, Nat.add_assoc]

theorem indexedSum_w {r s : ℕ} (L : Edge r s → ℕ) (i : Fin r) (j : Fin s) :
    indexedSum L (i,some (j,1)) = L (i,j,1) + L (i,j,2) + L (i,j,3) := by
  simp [indexedSum, Fintype.sum_prod_type, Fin.sum_univ_succ, edgeMap, ends,
    Sym2.mem_iff, Finset.sum_add_distrib, ite_and, Nat.add_assoc]

theorem indexedSum_v {r s : ℕ} (L : Edge r s → ℕ) (i : Fin r) (j : Fin s) :
    indexedSum L (i,some (j,2)) = L (i,j,3) + L (i,j,4) := by
  simp [indexedSum, Fintype.sum_prod_type, Fin.sum_univ_succ, edgeMap, ends,
    Sym2.mem_iff, Finset.sum_add_distrib, ite_and, Nat.add_assoc]

#print axioms indexedSum_hub
#print axioms indexedSum_u
#print axioms indexedSum_w
#print axioms indexedSum_v
end RFB
```

### `RFBAffine.lean`

```lean
import RFBSupply
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace RFB
abbrev Aff := ℤ × ℤ

def evalAff (k : ℤ) (p : Aff) : ℤ := p.1*k+p.2

def tradeCoeff : Fin 21 → Fin 5 → Aff := ![
  ![(10,-1), (3,2), (1,-3), (6,2), (7,-1)],
  ![(9,-1), (4,2), (2,-4), (4,3), (9,-2)],
  ![(9,1), (1,0), (3,4), (9,-3), (1,4)],
  ![(3,-3), (7,4), (4,-1), (2,-2), (8,3)],
  ![(3,0), (7,1), (4,1), (2,-1), (8,2)],
  ![(10,-2), (0,3), (7,-3), (6,1), (4,0)],
  ![(2,2), (8,-1), (3,-2), (2,4), (8,-3)],
  ![(6,-5), (4,6), (6,-1), (3,-4), (7,5)],
  ![(4,5), (6,-4), (6,0), (1,5), (9,-4)],
  ![(9,2), (1,-1), (2,5), (10,-3), (0,4)],
  ![(6,-6), (4,7), (6,-11), (3,5), (7,-4)],
  ![(8,0), (2,1), (7,3), (4,-3), (6,4)],
  ![(8,-2), (2,3), (1,3), (10,-5), (0,6)],
  ![(3,-1), (7,2), (6,-2), (0,1), (10,0)],
  ![(6,-3), (4,4), (8,-4), (1,1), (9,0)],
  ![(4,-5), (6,6), (1,2), (6,-7), (4,8)],
  ![(9,-5), (1,6), (6,-10), (6,5), (4,-4)],
  ![(9,3), (1,-2), (8,5), (4,-2), (6,3)],
  ![(0,5), (10,-4), (0,2), (3,3), (7,-2)],
  ![(7,0), (3,1), (6,-9), (4,9), (6,-8)],
  ![(8,1), (2,0), (9,4), (2,-3), (8,4)]
]

def removedCoeff : Fin 21 → Fin 5 → Aff := ![
  ![(10,0), (0,1), (7,0), (6,0), (4,1)],
  ![(9,0), (1,1), (6,-1), (6,1), (4,0)],
  ![(9,-1), (1,2), (6,-3), (6,2), (4,-1)],
  ![(9,-2), (1,3), (6,-5), (6,3), (4,-2)],
  ![(9,-3), (1,4), (6,-7), (6,4), (4,-3)],
  ![(9,-4), (1,5), (6,-9), (6,5), (4,-4)],
  ![(9,-5), (1,6), (6,-11), (6,6), (4,-5)],
  ![(8,5), (2,-4), (4,9), (7,-4), (3,5)],
  ![(8,4), (2,-3), (4,7), (7,-3), (3,4)],
  ![(8,3), (2,-2), (4,5), (7,-2), (3,3)],
  ![(8,2), (2,-1), (4,3), (7,-1), (3,2)],
  ![(10,-1), (0,2), (6,-2), (7,1), (3,0)],
  ![(10,-2), (0,3), (6,-4), (7,2), (3,-1)],
  ![(10,-3), (0,4), (6,-6), (7,3), (3,-2)],
  ![(10,-4), (0,5), (6,-8), (7,4), (3,-3)],
  ![(10,-5), (0,6), (6,-10), (7,5), (3,-4)],
  ![(9,4), (1,-3), (4,8), (8,-4), (2,5)],
  ![(9,3), (1,-2), (4,6), (8,-3), (2,4)],
  ![(9,2), (1,-1), (4,4), (8,-2), (2,3)],
  ![(9,1), (1,0), (4,2), (8,-1), (2,2)],
  ![(8,1), (2,0), (3,1), (8,0), (2,1)]
]

def tradeBlade (k : ℤ) (i : Fin 21) (t : Fin 5) : ℤ := evalAff k (tradeCoeff i t)

def RoleEquations (k : ℤ) (flipped : Prop) [Decidable flipped] (b : Fin 5 → ℤ) : Prop :=
  b 0 + b 1 = (if flipped then 13*k+1 else 10*k+1) ∧
  b 3 + b 4 = (if flipped then 13*k+1 else 10*k+1) ∧
  b 1 + b 2 + b 3 = (if flipped then 10*k+1 else 13*k+1)

def addAff (a b : Aff) : Aff := (a.1+b.1,a.2+b.2)

theorem eval_add (k : ℤ) (a b : Aff) :
    evalAff k (addAff a b) = evalAff k a + evalAff k b := by
  dsimp [evalAff, addAff]
  ring

theorem trade_roles_coeff : ∀ i : Fin 21,
    addAff (tradeCoeff i 0) (tradeCoeff i 1) = (if i.val < 2 then (13,1) else (10,1)) ∧
    addAff (tradeCoeff i 3) (tradeCoeff i 4) = (if i.val < 2 then (13,1) else (10,1)) ∧
    addAff (addAff (tradeCoeff i 1) (tradeCoeff i 2)) (tradeCoeff i 3) =
      (if i.val < 2 then (10,1) else (13,1)) := by decide

theorem trade_roles (k : ℤ) (i : Fin 21) :
    RoleEquations k (i.val < 2) (tradeBlade k i) := by
  obtain ⟨h1,h2,h3⟩ := trade_roles_coeff i
  have H1 := congrArg (evalAff k) h1
  have H2 := congrArg (evalAff k) h2
  have H3 := congrArg (evalAff k) h3
  simp only [eval_add] at H1 H2 H3
  by_cases hf : i.val < 2
  · simpa [RoleEquations, tradeBlade, evalAff, hf] using And.intro H1 (And.intro H2 H3)
  · simpa [RoleEquations, tradeBlade, evalAff, hf] using And.intro H1 (And.intro H2 H3)

def hub (b : Fin 5 → ℤ) : ℤ := b 0 + b 2 + b 4

def hubCoeff (i : Fin 21) : Aff :=
  addAff (addAff (tradeCoeff i 0) (tradeCoeff i 2)) (tradeCoeff i 4)

theorem eval_hub (k : ℤ) (i : Fin 21) :
    evalAff k (hubCoeff i) = hub (tradeBlade k i) := by
  simp only [hubCoeff, eval_add, hub, tradeBlade]

theorem trade_hub_coeff : ∀ g : Fin 7,
    addAff (addAff (hubCoeff ⟨3*g.val, by omega⟩) (hubCoeff ⟨3*g.val+1, by omega⟩))
      (hubCoeff ⟨3*g.val+2, by omega⟩) = (51,-3) := by decide

theorem trade_hub (k : ℤ) (g : Fin 7) :
    hub (tradeBlade k ⟨3*g.val, by omega⟩) +
    hub (tradeBlade k ⟨3*g.val+1, by omega⟩) +
    hub (tradeBlade k ⟨3*g.val+2, by omega⟩) = 3*(17*k-1) := by
  have h := congrArg (evalAff k) (trade_hub_coeff g)
  simp only [eval_add, eval_hub] at h
  rw [h]
  dsimp [evalAff]
  ring

#print axioms trade_roles
#print axioms trade_hub
end RFB
```

### `RFBColors.lean`

```lean
import RFBWeights

set_option linter.unusedSimpArgs false
namespace RFB

/-- A blade can have the ordinary or flipped peripheral colour roles. -/
def BladeRoles {r s : ℕ} (L : Edge r s → ℕ) (A B : ℕ) : Prop :=
  ∀ (i : Fin r) (j : Fin s),
    (L (i,j,0) + L (i,j,1) = A ∧ L (i,j,3) + L (i,j,4) = A ∧
      L (i,j,1) + L (i,j,2) + L (i,j,3) = B) ∨
    (L (i,j,0) + L (i,j,1) = B ∧ L (i,j,3) + L (i,j,4) = B ∧
      L (i,j,1) + L (i,j,2) + L (i,j,3) = A)

def HubSums {r s : ℕ} (L : Edge r s → ℕ) (H : ℕ) : Prop :=
  ∀ i : Fin r, ∑ j : Fin s, (L (i,j,0) + L (i,j,2) + L (i,j,4)) = H

def roleSum {r s : ℕ} (L : Edge r s → ℕ) (v : Vertex r s) : ℕ :=
  match v.2 with
  | none => ∑ j : Fin s, (L (v.1,j,0) + L (v.1,j,2) + L (v.1,j,4))
  | some (j,t) =>
    match t.val with
    | 0 => L (v.1,j,0) + L (v.1,j,1)
    | 1 => L (v.1,j,1) + L (v.1,j,2) + L (v.1,j,3)
    | _ => L (v.1,j,3) + L (v.1,j,4)

theorem indexedSum_eq_roleSum {r s : ℕ} (L : Edge r s → ℕ) (v : Vertex r s) :
    indexedSum L v = roleSum L v := by
  rcases v with ⟨i,v⟩
  cases v with
  | none => exact indexedSum_hub L i
  | some p =>
    rcases p with ⟨j,t⟩
    fin_cases t
    · exact indexedSum_u L i j
    · exact indexedSum_w L i j
    · exact indexedSum_v L i j

theorem chiLA_of_roleSum (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (L : Labeling r s)
    (hp : ∀ u v, (rFB r s).Adj u v → roleSum L.label u ≠ roleSum L.label v)
    (hc : (Finset.univ.image (roleSum L.label)).card = 3) :
    chiLA (rFB r s) = 3 := by
  apply chiLA_of_witness r s hr hs L.labelEquiv
  · apply proper_transfer
    simpa only [indexedSum_eq_roleSum] using hp
  · rw [colorCount_transfer]
    have heq : indexedSum L.label = roleSum L.label := funext (indexedSum_eq_roleSum L.label)
    rw [heq]
    exact hc

#print axioms indexedSum_eq_roleSum
#print axioms chiLA_of_roleSum
end RFB
```

### `RFBTrade.lean`

```lean
import RFBAffine
import Mathlib.Data.List.Sort
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB
def coeffLabels (f : Fin 21 → Fin 5 → Aff) : List Aff :=
  (List.ofFn f).flatMap List.ofFn

theorem trade_coeff_perm : (coeffLabels tradeCoeff).Perm (coeffLabels removedCoeff) := by
  decide

theorem trade_perm (k : ℤ) :
    ((coeffLabels tradeCoeff).map (evalAff k)).Perm
      ((coeffLabels removedCoeff).map (evalAff k)) :=
  trade_coeff_perm.map (evalAff k)

#print axioms trade_coeff_perm
#print axioms trade_perm
end RFB
```

### `RFBRemoved.lean`

```lean
import RFBAffine
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace RFB
def removedIndex (k : ℕ) (i : Fin 21) : ℕ :=
  if i.val < 7 then i.val+1 else if i.val < 16 then k+i.val-10 else 2*k+i.val-20

theorem removedIndex_bounds (k : ℕ) (hk : 11 ≤ k) (i : Fin 21) :
    1 ≤ removedIndex k i ∧ removedIndex k i ≤ 2*k := by
  have := i.isLt
  unfold removedIndex
  split_ifs <;> omega

theorem removedIndex_injective (k : ℕ) (hk : 11 ≤ k) :
    Function.Injective (removedIndex k) := by
  intro i j h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold removedIndex at h
  split_ifs at h <;> omega

#print axioms removedIndex_bounds
#print axioms removedIndex_injective
end RFB
```

### `RFBPool.lean`

```lean
import RFBTrade
import RFBRemoved
import RFBLabeling
import Mathlib.GroupTheory.Perm.ViaEmbedding

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

def tradeReindex (e : Fin 21 × Fin 5) : Fin 21 × Fin 5 :=
  (![
  ![(11,0), (10,4), (16,1), (2,3), (10,3)],
  ![(2,0), (19,2), (7,1), (10,2), (3,0)],
  ![(19,0), (19,1), (8,4), (4,0), (4,1)],
  ![(14,4), (14,3), (2,4), (9,1), (9,0)],
  ![(11,4), (11,3), (0,4), (10,1), (10,0)],
  ![(12,0), (12,1), (8,3), (1,3), (1,4)],
  ![(19,4), (19,3), (13,4), (17,4), (17,3)],
  ![(3,2), (17,2), (1,2), (15,4), (15,3)],
  ![(9,2), (12,2), (0,3), (5,1), (5,0)],
  ![(18,0), (18,1), (16,4), (13,0), (13,1)],
  ![(13,2), (8,2), (6,2), (7,4), (7,3)],
  ![(20,3), (20,4), (13,3), (4,4), (4,3)],
  ![(18,3), (18,4), (3,1), (15,0), (15,1)],
  ![(12,4), (12,3), (11,2), (0,1), (0,0)],
  ![(2,2), (18,2), (16,3), (1,1), (1,0)],
  ![(6,4), (6,3), (2,1), (4,2), (16,2)],
  ![(6,0), (6,1), (15,2), (5,3), (5,4)],
  ![(17,0), (17,1), (7,0), (3,4), (3,3)],
  ![(14,1), (14,0), (11,1), (9,4), (9,3)],
  ![(0,2), (20,2), (5,2), (7,2), (14,2)],
  ![(20,0), (20,1), (16,0), (8,1), (8,0)]
] : Fin 21 → Fin 5 → Fin 21 × Fin 5) e.1 e.2

def tradeInverse (e : Fin 21 × Fin 5) : Fin 21 × Fin 5 :=
  (![
  ![(13,4), (13,3), (19,0), (8,2), (4,2)],
  ![(14,4), (14,3), (7,2), (5,3), (5,4)],
  ![(1,0), (15,2), (14,0), (0,3), (3,2)],
  ![(1,4), (12,2), (7,0), (17,4), (17,3)],
  ![(2,3), (2,4), (15,3), (11,4), (11,3)],
  ![(8,4), (8,3), (19,2), (16,3), (16,4)],
  ![(16,0), (16,1), (10,2), (15,1), (15,0)],
  ![(17,2), (1,2), (19,3), (10,4), (10,3)],
  ![(20,4), (20,3), (10,1), (5,2), (2,2)],
  ![(3,4), (3,3), (8,0), (18,4), (18,3)],
  ![(4,4), (4,3), (1,3), (0,4), (0,1)],
  ![(0,0), (18,2), (13,2), (4,1), (4,0)],
  ![(5,0), (5,1), (8,1), (13,1), (13,0)],
  ![(9,3), (9,4), (10,0), (11,2), (6,2)],
  ![(18,1), (18,0), (19,4), (3,1), (3,0)],
  ![(12,3), (12,4), (16,2), (7,4), (7,3)],
  ![(20,2), (0,2), (15,4), (14,2), (9,2)],
  ![(17,0), (17,1), (7,1), (6,4), (6,3)],
  ![(9,0), (9,1), (14,1), (12,0), (12,1)],
  ![(2,0), (2,1), (1,1), (6,1), (6,0)],
  ![(20,0), (20,1), (19,1), (11,0), (11,1)]
] : Fin 21 → Fin 5 → Fin 21 × Fin 5) e.1 e.2

theorem tradeReindex_bijective : Function.Bijective tradeReindex := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · have hi : Function.LeftInverse tradeInverse tradeReindex := by
      rintro ⟨i,t⟩
      fin_cases i <;> fin_cases t <;> decide
    exact hi.injective
  · rfl

theorem tradeReindex_coeff (e : Fin 21 × Fin 5) :
    tradeCoeff e.1 e.2 = removedCoeff (tradeReindex e).1 (tradeReindex e).2 := by
  rcases e with ⟨i,t⟩
  fin_cases i <;> fin_cases t <;> decide

noncomputable def tradeEdgePerm : Equiv.Perm (Fin 21 × Fin 5) :=
  Equiv.ofBijective tradeReindex tradeReindex_bijective

def removedEdgeEmbedding (k : ℕ) (hk : 11 ≤ k) :
    (Fin 21 × Fin 5) ↪ (Fin (2*k) × Fin 5) where
  toFun e := (⟨removedIndex k e.1 - 1, by
    have := removedIndex_bounds k hk e.1; omega⟩, e.2)
  inj' := by
    intro a b hab
    have h1 := congrArg (fun e => e.1.val) hab
    have h2 := congrArg Prod.snd hab
    have ha := removedIndex_bounds k hk a.1
    have hb := removedIndex_bounds k hk b.1
    have hij : removedIndex k a.1 = removedIndex k b.1 := by
      dsimp at h1
      omega
    exact Prod.ext (removedIndex_injective k hk hij) h2

noncomputable def poolPerm (k : ℕ) (hk : 11 ≤ k) : Equiv.Perm (Fin (2*k) × Fin 5) :=
  tradeEdgePerm.viaEmbedding (removedEdgeEmbedding k hk)

noncomputable def poolLabel (k : ℕ) (hk : 11 ≤ k) (e : Fin (2*k) × Fin 5) : Fin (10*k) :=
  supplyLabel k hk (poolPerm k hk e)

theorem pool_bijective (k : ℕ) (hk : 11 ≤ k) : Function.Bijective (poolLabel k hk) :=
  (supply_bijective k hk).comp (poolPerm k hk).bijective

theorem pool_unchanged (k : ℕ) (hk : 11 ≤ k) (e : Fin (2*k) × Fin 5)
    (he : ∀ i : Fin 21, e.1.val+1 ≠ removedIndex k i) :
    poolLabel k hk e = supplyLabel k hk e := by
  unfold poolLabel poolPerm
  rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
  rintro ⟨a,ha⟩
  have hv := congrArg (fun e => e.1.val) ha
  have hb := removedIndex_bounds k hk a.1
  change removedIndex k a.1 - 1 = e.1.val at hv
  exact he a.1 (by omega)

/-- Any bijective blade grouping preserves the label permutation. The later grouping
proof must produce this equivalence and the required hub sums. -/
noncomputable def assembledLabeling (r s k : ℕ) (hk : 11 ≤ k) (hrs : 5*r*s = 10*k)
    (order : (Fin r × Fin s) ≃ Fin (2*k)) : Labeling r s where
  label e := (poolLabel k hk (order (e.1,e.2.1),e.2.2)).val + 1
  positive e := by omega
  bounded e := by have := (poolLabel k hk (order (e.1,e.2.1),e.2.2)).isLt; omega
  injective := by
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have hp : poolLabel k hk (order (i,j),t) = poolLabel k hk (order (i',j'),t') :=
      Fin.ext (by simpa using Nat.add_right_cancel h)
    have he := (pool_bijective k hk).injective hp
    have ho := order.injective (congrArg Prod.fst he)
    have ht := congrArg Prod.snd he
    have hi := congrArg Prod.fst ho
    have hj := congrArg Prod.snd ho
    simp_all

#print axioms pool_bijective
#print axioms pool_unchanged
#print axioms assembledLabeling
end RFB
```

### `RFBRoles.lean`

```lean
import RFBColors

set_option linter.unusedSimpArgs false
namespace RFB

theorem peripheral_mem {r s : ℕ} (L : Edge r s → ℕ) {A B : ℕ}
    (hb : BladeRoles L A B) (i : Fin r) (j : Fin s) (t : Fin 3) :
    roleSum L (i,some (j,t)) = A ∨ roleSum L (i,some (j,t)) = B := by
  obtain h | h := hb i j
  · fin_cases t <;> simp [roleSum, h]
  · fin_cases t <;> simp [roleSum, h]

theorem roles_proper {r s : ℕ} (L : Edge r s → ℕ) {A B H : ℕ}
    (hb : BladeRoles L A B) (hh : HubSums L H)
    (hAB : A ≠ B) (hAH : A ≠ H) (hBH : B ≠ H) :
    ∀ u v, (rFB r s).Adj u v → roleSum L u ≠ roleSum L v := by
  rintro ⟨i,u⟩ ⟨j,v⟩ ⟨hij,ha⟩
  change i = j at hij
  subst j
  cases u with
  | none =>
    cases v with
    | none => exact False.elim ha
    | some p =>
      rcases p with ⟨j,t⟩
      have hu : roleSum L (i,none) = H := hh i
      obtain hv | hv := peripheral_mem L hb i j t <;> rw [hu,hv]
      · exact hAH.symm
      · exact hBH.symm
  | some p =>
    rcases p with ⟨j,t⟩
    cases v with
    | none =>
      have hv : roleSum L (i,none) = H := hh i
      obtain hu | hu := peripheral_mem L hb i j t <;> rw [hu,hv]
      · exact hAH
      · exact hBH
    | some q =>
      rcases q with ⟨j',t'⟩
      change j = j' ∧ _ at ha
      obtain ⟨rfl,ha⟩ := ha
      obtain h | h := hb i j
      · fin_cases t <;> fin_cases t' <;> simp_all [roleSum, Ne.symm]
      · fin_cases t <;> fin_cases t' <;> simp_all [roleSum, Ne.symm]

theorem roles_count_le {r s : ℕ} (L : Edge r s → ℕ) {A B H : ℕ}
    (hb : BladeRoles L A B) (hh : HubSums L H) :
    (Finset.univ.image (roleSum L)).card ≤ 3 := by
  have hsub : Finset.univ.image (roleSum L) ⊆ ({A,B,H} : Finset ℕ) := by
    rintro a ha
    obtain ⟨⟨i,v⟩,_,rfl⟩ := Finset.mem_image.mp ha
    cases v with
    | none => simp only [roleSum, hh i]; simp
    | some p =>
      obtain h | h := peripheral_mem L hb i p.1 p.2 <;> simp [h]
  have h1 := Finset.card_insert_le A ({B,H} : Finset ℕ)
  have h2 := Finset.card_insert_le B ({H} : Finset ℕ)
  simp only [Finset.card_singleton] at h2
  exact (Finset.card_le_card hsub).trans (by omega)

theorem chiLA_of_roles (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (L : Labeling r s)
    (A B H : ℕ) (hb : BladeRoles L.label A B) (hh : HubSums L.label H)
    (hAB : A ≠ B) (hAH : A ≠ H) (hBH : B ≠ H) : chiLA (rFB r s) = 3 := by
  have hp := roles_proper L.label hb hh hAB hAH hBH
  have hprop : IsLocalAntimagic (rFB r s) L.labelEquiv := by
    apply proper_transfer
    simpa only [indexedSum_eq_roleSum] using hp
  have heq : indexedSum L.label = roleSum L.label := funext (indexedSum_eq_roleSum L.label)
  apply chiLA_of_witness r s hr hs L.labelEquiv hprop
  apply Nat.le_antisymm
  · rw [colorCount_transfer, heq]
    exact roles_count_le L.label hb hh
  · exact triangle_lower r s hr hs _ hprop

#print axioms chiLA_of_roles
end RFB
```

### `RFBCase2x5.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case2x5
def labels (e : Edge 2 5) : ℕ :=
  (![
  ![![49,2,47,1,50], ![34,16,25,10,40], ![31,19,14,18,32], ![33,17,21,13,37], ![38,12,28,11,39]],
  ![![46,5,42,3,48], ![36,15,29,6,45], ![26,24,4,23,27], ![43,8,35,7,44], ![30,20,22,9,41]]
] : Fin 2 → Fin 5 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,0,3), (0,0,1), (1,0,3), (1,2,2), (1,0,1), (1,1,3), (1,3,3), (1,3,1), (1,4,3), (0,1,3), (0,4,3), (0,4,1), (0,3,3), (0,2,2), (1,1,1), (0,1,1), (0,3,1), (0,2,3), (0,2,1), (1,4,1), (0,3,2), (1,4,2), (1,2,3), (1,2,1), (0,1,2), (1,2,0), (1,2,4), (0,4,2), (1,1,2), (1,4,0), (0,2,0), (0,2,4), (0,3,0), (0,1,0), (1,3,2), (1,1,0), (0,3,4), (0,4,0), (0,4,4), (0,1,4), (1,4,4), (1,0,2), (1,3,0), (1,3,4), (1,1,4), (1,0,0), (0,0,2), (1,0,4), (0,0,0), (0,0,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 2 5 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 2 5,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 50 51 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 518 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 2 5) = 3 :=
  chiLA_of_roles 2 5 (by decide) (by decide) labeling
    50 51 518 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case2x5
```

### `RFBCase2x7.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case2x7
def labels (e : Edge 2 7) : ℕ :=
  (![
  ![![69,2,67,1,70], ![66,5,62,3,68], ![64,7,57,6,65], ![36,35,4,31,40], ![43,27,30,14,56], ![38,32,10,29,41], ![44,26,25,20,50]],
  ![![60,11,51,8,63], ![58,13,45,12,59], ![47,23,39,9,61], ![48,22,34,15,55], ![52,18,37,16,54], ![42,28,19,24,46], ![49,21,33,17,53]]
] : Fin 2 → Fin 7 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,0,3), (0,0,1), (0,1,3), (0,3,2), (0,1,1), (0,2,3), (0,2,1), (1,0,3), (1,2,3), (0,5,2), (1,0,1), (1,1,3), (1,1,1), (0,4,3), (1,3,3), (1,4,3), (1,6,3), (1,4,1), (1,5,2), (0,6,3), (1,6,1), (1,3,1), (1,2,1), (1,5,3), (0,6,2), (0,6,1), (0,4,1), (1,5,1), (0,5,3), (0,4,2), (0,3,3), (0,5,1), (1,6,2), (1,3,2), (0,3,1), (0,3,0), (1,4,2), (0,5,0), (1,2,2), (0,3,4), (0,5,4), (1,5,0), (0,4,0), (0,6,0), (1,1,2), (1,5,4), (1,2,0), (1,3,0), (1,6,0), (0,6,4), (1,0,2), (1,4,0), (1,6,4), (1,4,4), (1,3,4), (0,4,4), (0,2,2), (1,1,0), (1,1,4), (1,0,0), (1,2,4), (0,1,2), (1,0,4), (0,2,0), (0,2,4), (0,1,0), (0,0,2), (0,1,4), (0,0,0), (0,0,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 2 7 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 2 7,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 70 71 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 1005 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 2 7) = 3 :=
  chiLA_of_roles 2 7 (by decide) (by decide) labeling
    70 71 1005 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case2x7
```

### `RFBCase2x9.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case2x9
def labels (e : Edge 2 9) : ℕ :=
  (![
  ![![60,31,82,5,86], ![51,40,62,16,75], ![32,59,56,3,88], ![30,61,8,49,42], ![22,69,36,13,78], ![15,76,38,4,87], ![10,81,23,14,77], ![65,53,9,29,89], ![63,55,1,35,83]],
  ![![74,17,90,11,80], ![54,37,57,24,67], ![50,41,58,19,72], ![48,43,68,7,84], ![44,47,26,45,46], ![27,64,2,52,39], ![25,66,34,18,73], ![21,70,28,20,71], ![12,79,33,6,85]]
] : Fin 2 → Fin 9 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,8,2), (1,5,2), (0,2,3), (0,5,3), (0,0,3), (1,8,3), (1,3,3), (0,3,2), (0,7,2), (0,6,0), (1,0,3), (1,8,0), (0,4,3), (0,6,3), (0,5,0), (0,1,3), (1,0,1), (1,6,3), (1,2,3), (1,7,3), (1,7,0), (0,4,0), (0,6,2), (1,1,3), (1,6,0), (1,4,2), (1,5,0), (1,7,2), (0,7,3), (0,3,0), (0,0,1), (0,2,0), (1,8,2), (1,6,2), (0,8,3), (0,4,2), (1,1,1), (0,5,2), (1,5,4), (0,1,1), (1,2,1), (0,3,4), (1,3,1), (1,4,0), (1,4,3), (1,4,4), (1,4,1), (1,3,0), (0,3,3), (1,2,0), (0,1,0), (1,5,3), (0,7,1), (1,1,0), (0,8,1), (0,2,2), (1,1,2), (1,2,2), (0,2,1), (0,0,0), (0,3,1), (0,1,2), (0,8,0), (1,5,1), (0,7,0), (1,6,1), (1,1,4), (1,3,2), (0,4,1), (1,7,1), (1,7,4), (1,2,4), (1,6,4), (1,0,0), (0,1,4), (0,5,1), (0,6,4), (0,4,4), (1,8,1), (1,0,4), (0,6,1), (0,0,2), (0,8,4), (1,3,4), (1,8,4), (0,0,4), (0,5,4), (0,2,4), (0,7,4), (1,0,2)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 2 9 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 2 9,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 91 118 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 1368 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 2 9) = 3 :=
  chiLA_of_roles 2 9 (by decide) (by decide) labeling
    91 118 1368 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case2x9
```

### `RFBCase2x11.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case2x11
def labels (e : Edge 2 11) : ℕ :=
  (![
  ![![109,35,8,68,76], ![98,46,18,47,97], ![100,11,37,96,15], ![33,78,45,21,90], ![108,3,74,67,44], ![24,87,31,26,85], ![101,10,27,107,4], ![86,25,14,105,6], ![32,79,64,1,110], ![63,48,84,12,99], ![102,9,93,42,69]],
  ![![30,81,43,20,91], ![61,50,65,29,82], ![49,62,66,16,95], ![60,51,55,38,73], ![88,23,80,41,70], ![39,72,13,59,52], ![94,17,56,71,40], ![5,106,2,36,75], ![77,34,57,53,58], ![89,22,103,19,92], ![104,7,54,83,28]]
] : Fin 2 → Fin 11 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,8,3), (1,7,2), (0,4,1), (0,6,4), (1,7,0), (0,7,4), (1,10,1), (0,0,2), (0,10,1), (0,6,1), (0,2,1), (0,9,3), (1,5,2), (0,7,2), (0,2,4), (1,2,3), (1,6,1), (0,1,2), (1,9,3), (1,0,3), (0,3,3), (1,9,1), (1,4,1), (0,5,0), (0,7,1), (0,5,3), (0,6,2), (1,10,4), (1,1,3), (1,0,0), (0,5,2), (0,8,0), (0,3,0), (1,8,1), (0,0,1), (1,7,3), (0,2,2), (1,3,3), (1,5,0), (1,6,4), (1,4,3), (0,10,3), (1,0,2), (0,4,4), (0,3,2), (0,1,1), (0,1,3), (0,9,1), (1,2,0), (1,1,1), (1,3,1), (1,5,4), (1,8,3), (1,10,2), (1,3,2), (1,6,2), (1,8,2), (1,8,4), (1,5,3), (1,3,0), (1,1,0), (1,2,1), (0,9,0), (0,8,2), (1,1,2), (1,2,2), (0,4,3), (0,0,3), (0,10,4), (1,4,4), (1,6,3), (1,5,1), (1,3,4), (0,4,2), (1,7,4), (0,0,4), (1,8,0), (0,3,1), (0,8,1), (1,4,2), (1,0,1), (1,1,4), (1,10,3), (0,9,2), (0,5,4), (0,7,0), (0,5,1), (1,4,0), (1,9,0), (0,3,4), (1,0,4), (1,9,4), (0,10,2), (1,6,0), (1,2,4), (0,2,3), (0,1,4), (0,1,0), (0,9,4), (0,2,0), (0,6,0), (0,10,0), (1,9,2), (1,10,0), (0,7,3), (1,7,1), (0,6,3), (0,4,0), (0,0,0), (0,8,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 2 11 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 2 11,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 111 144 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 2046 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 2 11) = 3 :=
  chiLA_of_roles 2 11 (by decide) (by decide) labeling
    111 144 2046 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case2x11
```

### `RFBCase4x3.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case4x3
def labels (e : Edge 4 3) : ℕ :=
  (![
  ![![11,50,28,1,60], ![42,37,3,21,58], ![40,39,2,20,59]],
  ![![47,14,52,13,48], ![29,32,16,31,30], ![6,55,19,5,56]],
  ![![34,27,45,7,54], ![25,36,33,10,51], ![17,44,9,26,35]],
  ![![38,23,41,15,46], ![18,43,24,12,49], ![8,53,22,4,57]]
] : Fin 4 → Fin 3 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,0,3), (0,2,2), (0,1,2), (3,2,3), (1,2,3), (1,2,0), (2,0,3), (3,2,0), (2,2,2), (2,1,3), (0,0,0), (3,1,3), (1,0,3), (1,0,1), (3,0,3), (1,1,2), (2,2,0), (3,1,0), (1,2,2), (0,2,3), (0,1,3), (3,2,2), (3,0,1), (3,1,2), (2,1,0), (2,2,3), (2,0,1), (0,0,2), (1,1,0), (1,1,4), (1,1,3), (1,1,1), (2,1,2), (2,0,0), (2,2,4), (2,1,1), (0,1,1), (3,0,0), (0,2,1), (0,2,0), (3,0,2), (0,1,0), (3,1,1), (2,2,1), (2,0,2), (3,0,4), (1,0,0), (1,0,4), (3,1,4), (0,0,1), (2,1,4), (1,0,2), (3,2,1), (2,0,4), (1,2,1), (1,2,4), (3,2,4), (0,1,4), (0,2,4), (0,0,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 4 3 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 4 3,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 61 79 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 303 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 4 3) = 3 :=
  chiLA_of_roles 4 3 (by decide) (by decide) labeling
    61 79 303 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case4x3
```

### `RFBCase4x5.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case4x5
def labels (e : Edge 4 5) : ℕ :=
  (![
  ![![82,19,97,15,86], ![50,51,44,36,65], ![26,75,8,48,53], ![73,58,4,39,92], ![70,61,2,38,93]],
  ![![66,35,62,34,67], ![56,45,57,29,72], ![32,69,52,10,91], ![22,79,46,6,95], ![18,83,28,20,81]],
  ![![76,25,99,7,94], ![42,59,55,17,84], ![30,71,33,27,74], ![24,77,49,5,96], ![16,85,9,37,64]],
  ![![54,47,63,21,80], ![41,60,68,3,98], ![23,78,40,13,88], ![14,87,43,1,100], ![12,89,31,11,90]]
] : Fin 4 → Fin 5 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(3,3,3), (0,4,2), (3,1,3), (0,3,2), (2,3,3), (1,3,3), (2,0,3), (0,2,2), (2,4,2), (1,2,3), (3,4,3), (3,4,0), (3,2,3), (3,3,0), (0,0,3), (2,4,0), (2,1,3), (1,4,0), (0,0,1), (1,4,3), (3,0,3), (1,3,0), (3,2,0), (2,3,0), (2,0,1), (0,2,0), (2,2,3), (1,4,2), (1,1,3), (2,2,0), (3,4,2), (1,2,0), (2,2,2), (1,0,3), (1,0,1), (0,1,3), (2,4,3), (0,4,3), (0,3,3), (3,2,2), (3,1,0), (2,1,0), (3,3,2), (0,1,2), (1,1,1), (1,3,2), (3,0,1), (0,2,3), (2,3,2), (0,1,0), (0,1,1), (1,2,2), (0,2,4), (3,0,0), (2,1,2), (1,1,0), (1,1,2), (0,3,1), (2,1,1), (3,1,1), (0,4,1), (1,0,2), (3,0,2), (2,4,4), (0,1,4), (1,0,0), (1,0,4), (3,1,2), (1,2,1), (0,4,0), (2,2,1), (1,1,4), (0,3,0), (2,2,4), (0,2,1), (2,0,0), (2,3,1), (3,2,1), (1,3,1), (3,0,4), (1,4,4), (0,0,0), (1,4,1), (2,1,4), (2,4,1), (0,0,4), (3,3,1), (3,2,4), (3,4,1), (3,4,4), (1,2,4), (0,3,4), (0,4,4), (2,0,4), (1,3,4), (2,3,4), (0,0,2), (3,1,4), (2,0,2), (3,3,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 4 5 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 4 5,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 101 131 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 845 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 4 5) = 3 :=
  chiLA_of_roles 4 5 (by decide) (by decide) labeling
    101 131 845 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case4x5
```

### `RFBCase4x7.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case4x7
def labels (e : Edge 4 7) : ℕ :=
  (![
  ![![139,44,11,86,97], ![125,58,24,59,124], ![127,14,46,123,18], ![42,99,57,27,114], ![61,80,84,19,122], ![119,22,69,92,49], ![131,10,66,107,34]],
  ![![79,62,83,38,103], ![128,13,33,137,4], ![41,100,82,1,140], ![98,43,75,65,76], ![134,7,72,104,37], ![133,8,70,105,36], ![132,9,68,106,35]],
  ![![138,3,95,85,56], ![112,29,101,53,88], ![110,31,17,135,6], ![5,136,2,45,96], ![113,28,130,25,116], ![120,21,71,91,50], ![118,23,67,93,48]],
  ![![39,102,55,26,115], ![30,111,40,32,109], ![78,63,73,47,94], ![81,60,108,15,126], ![51,90,16,77,64], ![121,20,74,89,52], ![129,12,117,54,87]]
] : Fin 4 → Fin 7 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(1,2,3), (2,3,2), (2,0,1), (1,1,4), (2,3,0), (2,2,4), (1,4,1), (1,5,1), (1,6,1), (0,6,1), (0,0,2), (3,6,1), (1,1,1), (0,2,1), (3,3,3), (3,4,2), (2,2,2), (0,2,4), (0,4,3), (3,5,1), (2,5,1), (0,5,1), (2,6,1), (0,1,2), (2,4,3), (3,0,3), (0,3,3), (2,4,1), (2,1,1), (3,1,0), (2,2,1), (3,1,3), (1,1,2), (0,6,4), (1,6,4), (1,5,4), (1,4,4), (1,0,3), (3,0,0), (3,1,2), (1,2,0), (0,3,0), (1,3,1), (0,0,1), (2,3,3), (0,2,2), (3,2,3), (2,6,4), (0,5,4), (2,5,4), (3,4,0), (3,5,4), (2,1,3), (3,6,3), (3,0,2), (2,0,4), (0,3,2), (0,1,1), (0,1,3), (3,3,1), (0,4,0), (1,0,1), (3,2,1), (3,4,4), (1,3,3), (0,6,2), (2,6,2), (1,6,2), (0,5,2), (1,5,2), (2,5,2), (1,4,2), (3,2,2), (3,5,2), (1,3,2), (1,3,4), (3,4,3), (3,2,0), (1,0,0), (0,4,1), (3,3,0), (1,2,2), (1,0,2), (0,4,2), (2,0,3), (0,0,3), (3,6,4), (2,1,4), (3,5,3), (3,4,1), (2,5,3), (0,5,3), (2,6,3), (3,2,4), (2,0,2), (2,3,4), (0,0,4), (1,3,0), (0,3,1), (1,2,1), (2,1,2), (3,0,1), (1,0,4), (1,4,3), (1,5,3), (1,6,3), (0,6,3), (3,3,2), (3,1,4), (2,2,0), (3,1,1), (2,1,0), (2,4,0), (0,3,4), (3,0,4), (2,4,4), (3,6,2), (2,6,0), (0,5,0), (2,5,0), (3,5,0), (0,4,4), (0,2,3), (0,1,4), (0,1,0), (3,3,4), (0,2,0), (1,1,0), (3,6,0), (2,4,2), (0,6,0), (1,6,0), (1,5,0), (1,4,0), (2,2,3), (2,3,1), (1,1,3), (2,0,0), (0,0,0), (1,2,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 4 7 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 4 7,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 141 183 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 1659 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 4 7) = 3 :=
  chiLA_of_roles 4 7 (by decide) (by decide) labeling
    141 183 1659 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case4x7
```

### `RFBCase6x3.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case6x3
def labels (e : Edge 6 3) : ℕ :=
  (![
  ![![27,64,48,6,85], ![71,47,2,42,76], ![56,62,1,28,90]],
  ![![51,40,68,10,81], ![38,53,29,36,55], ![17,74,35,9,82]],
  ![![46,45,65,8,83], ![32,59,52,7,84], ![19,72,15,31,60]],
  ![![50,41,63,14,77], ![37,54,43,21,70], ![3,88,26,4,87]],
  ![![34,57,39,22,69], ![33,58,49,11,80], ![30,61,44,13,78]],
  ![![67,24,89,5,86], ![18,73,20,25,66], ![12,79,23,16,75]]
] : Fin 6 → Fin 3 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(0,2,2), (0,1,2), (3,2,0), (3,2,3), (5,0,3), (0,0,3), (2,1,3), (2,0,3), (1,2,3), (1,0,3), (4,1,3), (5,2,0), (4,2,3), (3,0,3), (2,2,2), (5,2,3), (1,2,0), (5,1,0), (2,2,0), (5,1,2), (3,1,3), (4,0,3), (5,2,2), (5,0,1), (5,1,3), (3,2,2), (0,0,0), (0,2,3), (1,1,2), (4,2,0), (2,2,3), (2,1,0), (4,1,0), (4,0,0), (1,2,2), (1,1,3), (3,1,0), (1,1,0), (4,0,2), (1,0,1), (3,0,1), (0,1,3), (3,1,2), (4,2,2), (2,0,1), (2,0,0), (0,1,1), (0,0,2), (4,1,2), (3,0,0), (1,0,0), (2,1,2), (1,1,1), (3,1,1), (1,1,4), (0,2,0), (4,0,1), (4,1,1), (2,1,1), (2,2,4), (4,2,1), (0,2,1), (3,0,2), (0,0,1), (2,0,2), (5,1,4), (5,0,0), (1,0,2), (4,0,4), (3,1,4), (0,1,0), (2,2,1), (5,1,1), (1,2,1), (5,2,4), (0,1,4), (3,0,4), (4,2,4), (5,2,1), (4,1,4), (1,0,4), (1,2,4), (2,0,4), (2,1,4), (0,0,4), (5,0,4), (3,2,4), (3,2,1), (5,0,2), (0,2,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 6 3 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 6 3,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 91 118 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 456 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 6 3) = 3 :=
  chiLA_of_roles 6 3 (by decide) (by decide) labeling
    91 118 456 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case6x3
```

### `RFBCase6x5.lean`

```lean
import RFBRoles
import Mathlib.Data.Fin.VecNotation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace RFB.Case6x5
def labels (e : Edge 6 5) : ℕ :=
  (![
  ![![87,64,126,6,145], ![56,95,89,12,139], ![44,107,13,76,75], ![113,83,3,65,131], ![111,85,4,62,134]],
  ![![120,31,146,19,132], ![92,59,127,10,141], ![42,109,60,27,124], ![18,133,20,43,108], ![8,143,17,36,115]],
  ![![97,54,103,39,112], ![82,69,98,29,122], ![67,84,66,46,105], ![63,88,78,30,121], ![41,110,25,61,90]],
  ![![104,47,148,1,150], ![55,96,93,7,144], ![52,99,86,11,140], ![14,137,38,21,130], ![9,142,5,49,102]],
  ![![118,33,147,16,135], ![57,94,68,34,117], ![51,100,24,72,79], ![50,101,73,22,129], ![15,136,58,2,149]],
  ![![119,32,138,26,125], ![81,70,91,35,116], ![74,77,48,71,80], ![45,106,53,37,114], ![23,128,40,28,123]]
] : Fin 6 → Fin 5 → Fin 5 → ℕ) e.1 e.2.1 e.2.2

def inverse (n : ℕ) : ℕ × ℕ × ℕ :=
  ([(3,0,3), (4,4,3), (0,3,2), (0,4,2), (3,4,2), (0,0,3), (3,1,3), (1,4,0), (3,4,0), (1,1,3), (3,2,3), (0,1,3), (0,2,2), (3,3,0), (4,4,0), (4,0,3), (1,4,2), (1,3,0), (1,0,3), (1,3,2), (3,3,3), (4,3,3), (5,4,0), (4,2,2), (2,4,2), (5,0,3), (1,2,3), (5,4,3), (2,1,3), (2,3,3), (1,0,1), (5,0,1), (4,0,1), (4,1,3), (5,1,3), (1,4,3), (5,3,3), (3,3,2), (2,0,3), (5,4,2), (2,4,0), (1,2,0), (1,3,3), (0,2,0), (5,3,0), (2,2,3), (3,0,1), (5,2,2), (3,4,3), (4,3,0), (4,2,0), (3,2,0), (5,3,2), (2,0,1), (3,1,0), (0,1,0), (4,1,0), (4,4,2), (1,1,1), (1,2,2), (2,4,3), (0,4,3), (2,3,0), (0,0,1), (0,3,3), (2,2,2), (2,2,0), (4,1,2), (2,1,1), (5,1,1), (5,2,3), (4,2,3), (4,3,2), (5,2,0), (0,2,4), (0,2,3), (5,2,1), (2,3,2), (4,2,4), (5,2,4), (5,1,0), (2,1,0), (0,3,1), (2,2,1), (0,4,1), (3,2,2), (0,0,0), (2,3,1), (0,1,2), (2,4,4), (5,1,2), (1,1,0), (3,1,2), (4,1,1), (0,1,1), (3,1,1), (2,0,0), (2,1,2), (3,2,1), (4,2,1), (4,3,1), (3,4,4), (2,0,2), (3,0,0), (2,2,4), (5,3,1), (0,2,1), (1,3,4), (1,2,1), (2,4,1), (0,4,0), (2,0,4), (0,3,0), (5,3,4), (1,4,4), (5,1,4), (4,1,4), (4,0,0), (5,0,0), (1,0,0), (2,3,4), (2,1,4), (5,4,4), (1,2,4), (5,0,4), (0,0,2), (1,1,2), (5,4,1), (4,3,4), (3,3,4), (0,3,4), (1,0,4), (1,3,1), (0,4,4), (4,0,4), (4,4,1), (3,3,1), (5,0,2), (0,1,4), (3,2,4), (1,1,4), (3,4,1), (1,4,1), (3,1,4), (0,0,4), (1,0,2), (4,0,2), (3,0,2), (4,4,4), (3,0,4)] : List (ℕ × ℕ × ℕ)).getD n (0,0,0)

def labeling : Labeling 6 5 where
  label := labels
  positive := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  bounded := by
    rintro ⟨i,j,t⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
  injective := by
    have hi : ∀ e : Edge 6 5,
        inverse (labels e - 1) = (e.1.val,e.2.1.val,e.2.2.val) := by
      rintro ⟨i,j,t⟩
      fin_cases i <;> fin_cases j <;> fin_cases t <;> decide
    rintro ⟨i,j,t⟩ ⟨i',j',t'⟩ h
    have he := (hi (i,j,t)).symm.trans
      ((congrArg inverse (congrArg (fun n : ℕ => n-1) h)).trans (hi (i',j',t')))
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun e => e.2.1) he
    have h3 := congrArg (fun e => e.2.2) he
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem roles : BladeRoles labels 151 196 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
theorem hubs : HubSums labels 1270 := by
  intro i
  fin_cases i <;> decide

theorem endpoint : chiLA (rFB 6 5) = 3 :=
  chiLA_of_roles 6 5 (by decide) (by decide) labeling
    151 196 1270 roles hubs (by decide) (by decide) (by decide)
#print axioms endpoint
end RFB.Case6x5
```

### `RFBCentres.lean`

```lean
import RFBRemoved

set_option linter.unusedSimpArgs false
namespace RFB

theorem removedIndex_range (k n : ℕ) (hk : 11 ≤ k) :
    (∃ j : Fin 21, removedIndex k j = n) ↔
      (1 ≤ n ∧ n ≤ 7) ∨ (k-3 ≤ n ∧ n ≤ k+5) ∨ (2*k-4 ≤ n ∧ n ≤ 2*k) := by
  constructor
  · rintro ⟨j,rfl⟩
    have := j.isLt
    unfold removedIndex
    split_ifs <;> omega
  · rintro (h | h | h)
    · refine ⟨⟨n-1, by omega⟩, ?_⟩
      simp only [removedIndex]
      split_ifs <;> omega
    · refine ⟨⟨n+10-k, by omega⟩, ?_⟩
      simp only [removedIndex]
      split_ifs <;> omega
    · refine ⟨⟨n+20-2*k, by omega⟩, ?_⟩
      simp only [removedIndex]
      split_ifs <;> omega

def IsKept (k : ℕ) (i : Fin (2*k)) : Prop :=
  ∀ j : Fin 21, i.val+1 ≠ removedIndex k j

instance (k : ℕ) : DecidablePred (IsKept k) := fun i => by
  unfold IsKept
  infer_instance

abbrev Kept (k : ℕ) := {i : Fin (2*k) // IsKept k i}

theorem kept_iff_centre_bounds (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) :
    IsKept k i ↔ 4*k+10 ≤ supply k (i.val+1) 2 ∧ supply k (i.val+1) 2 ≤ 6*k-12 := by
  have hi := i.isLt
  have hr := removedIndex_range k (i.val+1) hk
  have hkept : IsKept k i ↔ ¬∃j : Fin 21, removedIndex k j = i.val+1 := by
    simp only [IsKept, not_exists, ne_eq, eq_comm]
  rw [hkept, hr]
  simp [supply]
  split_ifs <;> omega

#print axioms removedIndex_range
#print axioms kept_iff_centre_bounds
end RFB

namespace RFB

def centreColumn (k c : ℕ) : ℕ :=
  if c % 2 = 1 then (6*k+3-c)/2 else (8*k-c)/2

theorem centreColumn_spec (k c : ℕ) (hk : 11 ≤ k)
    (hc : 4*k+10 ≤ c) (hc' : c ≤ 6*k-12) :
    1 ≤ centreColumn k c ∧ centreColumn k c ≤ 2*k ∧
      supply k (centreColumn k c) 2 = c := by
  have hm : c % 2 < 2 := Nat.mod_lt c (by decide)
  unfold centreColumn
  split_ifs with hp
  · simp [supply]
    split_ifs <;> omega
  · simp [supply]
    split_ifs <;> omega

def centreLabel (k : ℕ) (hk : 11 ≤ k) (i : Kept k) : Fin (2*k-21) :=
  ⟨supply k (i.val.val+1) 2 - (4*k+10), by
    have h := (kept_iff_centre_bounds k hk i.val).mp i.property
    omega⟩

theorem centreLabel_bijective (k : ℕ) (hk : 11 ≤ k) : Function.Bijective (centreLabel k hk) := by
  constructor
  · intro a b hab
    have ha := (kept_iff_centre_bounds k hk a.val).mp a.property
    have hb := (kept_iff_centre_bounds k hk b.val).mp b.property
    have hv := congrArg Fin.val hab
    change supply k (a.val.val+1) 2 - (4*k+10) =
      supply k (b.val.val+1) 2 - (4*k+10) at hv
    have he : supply k (a.val.val+1) 2 = supply k (b.val.val+1) 2 := by omega
    have hi := a.val.isLt
    have hj := b.val.isLt
    obtain ⟨hij,_⟩ := supply_injective_aux k (a.val.val+1) (b.val.val+1) hk
      (by omega) (by omega) (by omega) (by omega) 2 2 he
    apply Subtype.ext
    apply Fin.ext
    omega
  · intro c
    let C := 4*k+10+c.val
    have hc : 4*k+10 ≤ C := by omega
    have hc' : C ≤ 6*k-12 := by have := c.isLt; omega
    have ht := centreColumn_spec k C hk hc hc'
    let i : Fin (2*k) := ⟨centreColumn k C-1, by omega⟩
    have hi : i.val+1 = centreColumn k C := by dsimp [i]; omega
    have hsi : supply k (i.val+1) 2 = C := by rw [hi]; exact ht.2.2
    have hkeep : IsKept k i := by
      apply (kept_iff_centre_bounds k hk i).mpr
      rw [hsi]
      exact ⟨hc,hc'⟩
    refine ⟨⟨i,hkeep⟩, Fin.ext ?_⟩
    change supply k (i.val+1) 2 - (4*k+10) = c.val
    rw [hsi]
    dsimp [C]
    omega

noncomputable def centreEquiv (k : ℕ) (hk : 11 ≤ k) : Kept k ≃ Fin (2*k-21) :=
  Equiv.ofBijective (centreLabel k hk) (centreLabel_bijective k hk)

theorem card_kept (k : ℕ) (hk : 11 ≤ k) : Fintype.card (Kept k) = 2*k-21 := by
  rw [Fintype.card_congr (centreEquiv k hk), Fintype.card_fin]

#print axioms centreColumn_spec
#print axioms centreLabel_bijective
#print axioms card_kept
end RFB
```

### `RFBSupplyCast.lean`

```lean
import RFBRemoved
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

def supplyZ (k i : ℤ) (t : Fin 5) : ℤ :=
  if i = 1 then (![10*k,1,7*k,6*k,4*k+1] : Fin 5 → ℤ) t
  else if i ≤ k then (![9*k+2-i,k+i-1,6*k+3-2*i,6*k+i-1,4*k+2-i] : Fin 5 → ℤ) t
  else if i < 2*k then (![11*k-i,i-k+1,8*k-2*i,6*k+i,4*k+1-i] : Fin 5 → ℤ) t
  else (![8*k+1,2*k,3*k+1,8*k,2*k+1] : Fin 5 → ℤ) t

theorem supply_cast (k i : ℕ) (_hk : 11 ≤ k) (hi : 1 ≤ i) (hi' : i ≤ 2*k) (t : Fin 5) :
    (supply k i t : ℤ) = supplyZ (k : ℤ) (i : ℤ) t := by
  fin_cases t <;> simp [supply, supplyZ] <;> split_ifs <;> omega

#print axioms supply_cast
end RFB
```

### `RFBRemovedBlock0.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_block0 (k : ℕ) (hk : 11 ≤ k) (i : Fin 7) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff ⟨i.val, by omega⟩ t) =
      (supply k (removedIndex k ⟨i.val, by omega⟩) t : ℤ) := by
  have hb := removedIndex_bounds k hk (⟨i.val, by omega⟩ : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases i <;> fin_cases t <;>
    simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_block0
end RFB
```

### `RFBRemovedBlock1.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_block1 (k : ℕ) (hk : 11 ≤ k) (i : Fin 7) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff ⟨i.val+7, by omega⟩ t) =
      (supply k (removedIndex k ⟨i.val+7, by omega⟩) t : ℤ) := by
  have hb := removedIndex_bounds k hk (⟨i.val+7, by omega⟩ : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases i <;> fin_cases t <;>
    simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_block1
end RFB
```

### `RFBRemovedColumn14.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column14 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 14 t) =
      (supply k (removedIndex k 14) t : ℤ) := by
  have hb := removedIndex_bounds k hk (14 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column14
end RFB
```

### `RFBRemovedColumn15.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column15 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 15 t) =
      (supply k (removedIndex k 15) t : ℤ) := by
  have hb := removedIndex_bounds k hk (15 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column15
end RFB
```

### `RFBRemovedColumn16.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column16 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 16 t) =
      (supply k (removedIndex k 16) t : ℤ) := by
  have hb := removedIndex_bounds k hk (16 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column16
end RFB
```

### `RFBRemovedColumn17.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column17 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 17 t) =
      (supply k (removedIndex k 17) t : ℤ) := by
  have hb := removedIndex_bounds k hk (17 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column17
end RFB
```

### `RFBRemovedColumn18.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column18 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 18 t) =
      (supply k (removedIndex k 18) t : ℤ) := by
  have hb := removedIndex_bounds k hk (18 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column18
end RFB
```

### `RFBRemovedColumn19.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column19 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 19 t) =
      (supply k (removedIndex k 19) t : ℤ) := by
  have hb := removedIndex_bounds k hk (19 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column19
end RFB
```

### `RFBRemovedColumn20.lean`

```lean
import RFBSupplyCast
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RFB

theorem removed_eval_column20 (k : ℕ) (hk : 11 ≤ k) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff 20 t) =
      (supply k (removedIndex k 20) t : ℤ) := by
  have hb := removedIndex_bounds k hk (20 : Fin 21)
  rw [supply_cast k _ hk hb.1 hb.2]
  fin_cases t <;> simp [evalAff, removedCoeff, removedIndex, supplyZ] <;> split_ifs <;> omega

#print axioms removed_eval_column20
end RFB
```

### `RFBRemovedBlock2.lean`

```lean
import RFBRemovedColumn14
import RFBRemovedColumn15
import RFBRemovedColumn16
import RFBRemovedColumn17
import RFBRemovedColumn18
import RFBRemovedColumn19
import RFBRemovedColumn20
namespace RFB

theorem removed_eval_block2 (k : ℕ) (hk : 11 ≤ k) (i : Fin 7) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff ⟨i.val+14, by omega⟩ t) =
      (supply k (removedIndex k ⟨i.val+14, by omega⟩) t : ℤ) := by
  fin_cases i
  · exact removed_eval_column14 k hk t
  · exact removed_eval_column15 k hk t
  · exact removed_eval_column16 k hk t
  · exact removed_eval_column17 k hk t
  · exact removed_eval_column18 k hk t
  · exact removed_eval_column19 k hk t
  · exact removed_eval_column20 k hk t

#print axioms removed_eval_block2
end RFB
```

### `RFBRemovedEval.lean`

```lean
import RFBRemovedBlock0
import RFBRemovedBlock1
import RFBRemovedBlock2
namespace RFB

theorem removed_eval (k : ℕ) (hk : 11 ≤ k) (i : Fin 21) (t : Fin 5) :
    evalAff (k : ℤ) (removedCoeff i t) = (supply k (removedIndex k i) t : ℤ) := by
  by_cases h0 : i.val < 7
  · exact removed_eval_block0 k hk ⟨i.val,h0⟩ t
  by_cases h1 : i.val < 14
  · have h := removed_eval_block1 k hk ⟨i.val-7, by omega⟩ t
    have hi : (⟨i.val-7+7, by omega⟩ : Fin 21) = i := by
      apply Fin.ext
      dsimp
      omega
    simpa only [hi] using h
  · have h := removed_eval_block2 k hk ⟨i.val-14, by omega⟩ t
    have hi : (⟨i.val-14+14, by omega⟩ : Fin 21) = i := by
      apply Fin.ext
      dsimp
      omega
    simpa only [hi] using h

#print axioms removed_eval
end RFB
```

### `RFBPoolEval.lean`

```lean
import RFBPool
import RFBRemovedEval
namespace RFB
theorem pool_removed (k : ℕ) (hk : 11 ≤ k) (e : Fin 21 × Fin 5) :
    ((poolLabel k hk (removedEdgeEmbedding k hk e)).val : ℤ) + 1 =
      tradeBlade (k : ℤ) e.1 e.2 := by
  unfold poolLabel poolPerm
  rw [Equiv.Perm.viaEmbedding_apply]
  change ((supply k (removedIndex k (tradeReindex e).1 - 1 + 1)
    (tradeReindex e).2 - 1 : ℕ) : ℤ) + 1 = _
  have hi := removedIndex_bounds k hk (tradeReindex e).1
  have he : removedIndex k (tradeReindex e).1 - 1 + 1 =
      removedIndex k (tradeReindex e).1 := by omega
  rw [he]
  have hb := supply_bounds k (removedIndex k (tradeReindex e).1) hk hi.1 hi.2
    (tradeReindex e).2
  rw [tradeBlade, tradeReindex_coeff, removed_eval k hk]
  omega

#print axioms pool_removed
end RFB
```

### `RFBExceptions.lean`

```lean
import RFBSmallest
import RFBCase2x5
import RFBCase2x7
import RFBCase2x9
import RFBCase2x11
import RFBCase4x3
import RFBCase4x5
import RFBCase4x7
import RFBCase6x3
import RFBCase6x5

namespace RFB

theorem exceptional_cases (r s : ℕ)
    (h : (r = 2 ∧ s = 3) ∨
      (r = 2 ∧ s = 5) ∨
      (r = 2 ∧ s = 7) ∨
      (r = 2 ∧ s = 9) ∨
      (r = 2 ∧ s = 11) ∨
      (r = 4 ∧ s = 3) ∨
      (r = 4 ∧ s = 5) ∨
      (r = 4 ∧ s = 7) ∨
      (r = 6 ∧ s = 3) ∨
      (r = 6 ∧ s = 5)) :
    chiLA (rFB r s) = 3 := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨rfl,rfl⟩ := h
    exact smallest_case
  · obtain ⟨rfl,rfl⟩ := h
    exact Case2x5.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case2x7.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case2x9.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case2x11.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case4x3.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case4x5.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case4x7.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case6x3.endpoint
  · obtain ⟨rfl,rfl⟩ := h
    exact Case6x5.endpoint

#print axioms exceptional_cases
end RFB
```

### `RFBTriples.lean`

```lean
import RFBSupply

set_option linter.unusedSimpArgs false
namespace RFB

/-- Equal-sum triples for h=2t+1, with one label from each interval of length h. -/
def triple (t i : ℕ) (j : Fin 3) : ℕ :=
  match j.val with
  | 0 => i+1
  | 1 => if i ≤ t then 3*t+i+2 else t+i+1
  | _ => if i ≤ t then 6*t+3-2*i else 8*t+4-2*i

theorem triple_bounds (t : ℕ) (i : Fin (2*t+1)) (j : Fin 3) :
    0 < triple t i.val j ∧ triple t i.val j ≤ 3*(2*t+1) := by
  have := i.isLt
  fin_cases j <;> simp only [triple] <;> (try split_ifs) <;> omega

def tripleLabel (t : ℕ) (e : Fin (2*t+1) × Fin 3) : Fin (3*(2*t+1)) :=
  ⟨triple t e.1.val e.2 - 1, by have := triple_bounds t e.1 e.2; omega⟩

theorem tripleLabel_bijective (t : ℕ) : Function.Bijective (tripleLabel t) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨i,j⟩ ⟨i',j'⟩ h
    have hi := i.isLt
    have hi' := i'.isLt
    have hb := triple_bounds t i j
    have hb' := triple_bounds t i' j'
    have hv := congrArg Fin.val h
    change triple t i.val j - 1 = triple t i'.val j' - 1 at hv
    have heq : triple t i.val j = triple t i'.val j' := by omega
    have hout : i.val = i'.val ∧ j = j' := by
      fin_cases j <;> fin_cases j' <;> simp only [triple] at heq <;>
        (try split_ifs at heq) <;> constructor <;> omega
    exact Prod.ext (Fin.ext hout.1) hout.2
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega

theorem triple_sum (t : ℕ) (i : Fin (2*t+1)) :
    triple t i.val 0 + triple t i.val 1 + triple t i.val 2 = 9*t+6 := by
  have := i.isLt
  simp [triple]
  split_ifs <;> omega

#print axioms tripleLabel_bijective
#print axioms triple_sum
end RFB
```

### `RFBPoolProperties.lean`

```lean
import RFBPoolEval
import RFBCentres

set_option linter.unusedSimpArgs false
namespace RFB

noncomputable def poolBlade (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) (t : Fin 5) : ℕ :=
  (poolLabel k hk (i,t)).val + 1

def removedColumn (k : ℕ) (hk : 11 ≤ k) (j : Fin 21) : Fin (2*k) :=
  ⟨removedIndex k j-1, by have := removedIndex_bounds k hk j; omega⟩

theorem supply_value (k : ℕ) (hk : 11 ≤ k) (e : Fin (2*k) × Fin 5) :
    (supplyLabel k hk e).val+1 = supply k (e.1.val+1) e.2 := by
  have := supply_bounds k (e.1.val+1) hk (by omega) (by have := e.1.isLt; omega) e.2
  dsimp [supplyLabel]
  omega

theorem pool_kept_value (k : ℕ) (hk : 11 ≤ k) (i : Kept k) (t : Fin 5) :
    poolBlade k hk i.val t = supply k (i.val.val+1) t := by
  unfold poolBlade
  rw [pool_unchanged k hk (i.val,t) i.property, supply_value]

theorem pool_ordinary (k : ℕ) (hk : 11 ≤ k) (i : Kept k) :
    poolBlade k hk i.val 0 + poolBlade k hk i.val 1 = 10*k+1 ∧
    poolBlade k hk i.val 3 + poolBlade k hk i.val 4 = 10*k+1 ∧
    poolBlade k hk i.val 1 + poolBlade k hk i.val 2 + poolBlade k hk i.val 3 = 13*k+1 := by
  simp only [pool_kept_value]
  exact supply_ordinary k (i.val.val+1) hk (by omega) (by have := i.val.isLt; omega)

theorem pool_trade_value (k : ℕ) (hk : 11 ≤ k) (i : Fin 21) (t : Fin 5) :
    (poolBlade k hk (removedColumn k hk i) t : ℤ) = tradeBlade (k : ℤ) i t := by
  have h := pool_removed k hk (i,t)
  change ((poolLabel k hk (removedColumn k hk i,t)).val : ℤ)+1 = _ at h
  simpa only [poolBlade, Nat.cast_add, Nat.cast_one] using h

theorem pool_trade_roles (k : ℕ) (hk : 11 ≤ k) (i : Fin 21) :
    RoleEquations (k : ℤ) (i.val < 2)
      (fun t => (poolBlade k hk (removedColumn k hk i) t : ℤ)) := by
  have heq : (fun t => (poolBlade k hk (removedColumn k hk i) t : ℤ)) =
      tradeBlade (k : ℤ) i := funext (pool_trade_value k hk i)
  rw [heq]
  exact trade_roles (k : ℤ) i

theorem pool_trade_hub (k : ℕ) (hk : 11 ≤ k) (g : Fin 7) :
    hub (fun t => (poolBlade k hk (removedColumn k hk ⟨3*g.val, by omega⟩) t : ℤ)) +
    hub (fun t => (poolBlade k hk (removedColumn k hk ⟨3*g.val+1, by omega⟩) t : ℤ)) +
    hub (fun t => (poolBlade k hk (removedColumn k hk ⟨3*g.val+2, by omega⟩) t : ℤ)) =
      3*(17*(k : ℤ)-1) := by
  have heq (i : Fin 21) : (fun t => (poolBlade k hk (removedColumn k hk i) t : ℤ)) =
      tradeBlade (k : ℤ) i := funext (pool_trade_value k hk i)
  simp only [heq]
  exact trade_hub (k : ℤ) g

#print axioms pool_ordinary
#print axioms pool_trade_value
#print axioms pool_trade_roles
#print axioms pool_trade_hub
end RFB
```

### `RFBPadding.lean`

```lean
import RFBTriples
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false
namespace RFB

abbrev PadRole (u : ℕ) := Fin 3 ⊕ (Fin u × Fin 2)

def pairVal (t u : ℕ) (q : Fin u) (i : Fin (2*t+1)) : ℕ :=
  (finProdFinEquiv (q,i)).val+1

theorem pairVal_bounds (t u : ℕ) (q : Fin u) (i : Fin (2*t+1)) :
    0 < pairVal t u q i ∧ pairVal t u q i ≤ u*(2*t+1) := by
  have h := (finProdFinEquiv (q,i)).isLt
  dsimp [pairVal]
  omega

def padNat (t u : ℕ) (i : Fin (2*t+1)) : PadRole u → ℕ
  | .inl j => u*(2*t+1) + triple t i.val j
  | .inr (q,b) => if b.val = 0 then pairVal t u q i
      else (2*u+3)*(2*t+1)+1-pairVal t u q i

theorem pad_bounds (t u : ℕ) (i : Fin (2*t+1)) (j : PadRole u) :
    0 < padNat t u i j ∧ padNat t u i j ≤ (2*u+3)*(2*t+1) := by
  have hN : (2*u+3)*(2*t+1) = 2*(u*(2*t+1))+3*(2*t+1) := by ring
  cases j with
  | inl j => have := triple_bounds t i j; dsimp [padNat]; omega
  | inr p =>
    rcases p with ⟨q,b⟩
    have := pairVal_bounds t u q i
    dsimp [padNat]
    split_ifs <;> omega

def padLabel (t u : ℕ) (e : Fin (2*t+1) × PadRole u) : Fin ((2*u+3)*(2*t+1)) :=
  ⟨padNat t u e.1 e.2-1, by have := pad_bounds t u e.1 e.2; omega⟩

theorem padLabel_injective (t u : ℕ) : Function.Injective (padLabel t u) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have hb := pad_bounds t u i j
  have hb' := pad_bounds t u i' j'
  have hv := congrArg Fin.val h
  change padNat t u i j - 1 = padNat t u i' j' - 1 at hv
  have he : padNat t u i j = padNat t u i' j' := by omega
  have hN : (2*u+3)*(2*t+1) = 2*(u*(2*t+1))+3*(2*t+1) := by ring
  cases j with
  | inl a =>
    have ha := triple_bounds t i a
    cases j' with
    | inl a' =>
      have heq : tripleLabel t (i,a) = tripleLabel t (i',a') := by
        apply Fin.ext
        dsimp [padNat] at he
        dsimp [tripleLabel]
        omega
      have hi := (tripleLabel_bijective t).injective heq
      obtain ⟨hii,haa⟩ := Prod.mk.inj hi
      cases hii
      cases haa
      rfl
    | inr p =>
      rcases p with ⟨q,b⟩
      have := pairVal_bounds t u q i'
      dsimp [padNat] at he
      split_ifs at he <;> omega
  | inr p =>
    rcases p with ⟨q,b⟩
    have hq := pairVal_bounds t u q i
    cases j' with
    | inl a' =>
      have ha := triple_bounds t i' a'
      dsimp [padNat] at he
      split_ifs at he <;> omega
    | inr p' =>
      rcases p' with ⟨q',b'⟩
      have hq' := pairVal_bounds t u q' i'
      have hbb : b = b' := by
        fin_cases b <;> fin_cases b' <;> simp [padNat] at he ⊢ <;> omega
      subst b'
      have hx : pairVal t u q i = pairVal t u q' i' := by
        dsimp [padNat] at he
        split_ifs at he <;> omega
      have hp : finProdFinEquiv (q,i) = finProdFinEquiv (q',i') := by
        apply Fin.ext
        dsimp [pairVal] at hx
        omega
      have hi := finProdFinEquiv.injective hp
      obtain ⟨hqq,hii⟩ := Prod.mk.inj hi
      cases hqq
      cases hii
      rfl

theorem padLabel_bijective (t u : ℕ) : Function.Bijective (padLabel t u) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨padLabel_injective t u, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

theorem pad_pair_sum (t u : ℕ) (i : Fin (2*t+1)) (q : Fin u) :
    padNat t u i (.inr (q,0)) + padNat t u i (.inr (q,1)) = (2*u+3)*(2*t+1)+1 := by
  have hb := pairVal_bounds t u q i
  have hN : (2*u+3)*(2*t+1) = 2*(u*(2*t+1))+3*(2*t+1) := by ring
  simp [padNat]
  omega

theorem pad_row_sum (t u : ℕ) (i : Fin (2*t+1)) :
    2*(∑ j : PadRole u, padNat t u i j) =
      (2*u+3)*((2*u+3)*(2*t+1)+1) := by
  have hl : (∑ j : Fin 3, padNat t u i (.inl j)) = 3*(u*(2*t+1))+9*t+6 := by
    have ht := triple_sum t i
    rw [Fin.sum_univ_three]
    simp only [padNat]
    omega
  have hr : (∑ p : Fin u × Fin 2, padNat t u i (.inr p)) =
      u*((2*u+3)*(2*t+1)+1) := by
    rw [Fintype.sum_prod_type]
    have he (q : Fin u) : (∑ b : Fin 2, padNat t u i (.inr (q,b))) =
        (2*u+3)*(2*t+1)+1 := by
      simpa [Fin.sum_univ_succ] using pad_pair_sum t u i q
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fintype.sum_sum_type, hl, hr]
  ring

#print axioms padLabel_bijective
#print axioms pad_row_sum
end RFB
```

### `RFBPartition.lean`

```lean
import RFBPadding
import Mathlib.Tactic.Linarith

namespace RFB

noncomputable def padRoleEquiv (u : ℕ) : Fin (2*u+3) ≃ PadRole u :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod]; omega)

noncomputable def partitionEquiv (t u : ℕ) :
    (Fin (2*t+1) × Fin (2*u+3)) ≃ Fin ((2*t+1)*(2*u+3)) :=
  ((Equiv.prodCongr (Equiv.refl _) (padRoleEquiv u)).trans
    (Equiv.ofBijective (padLabel t u) (padLabel_bijective t u))).trans
      (finCongr (Nat.mul_comm _ _))

theorem partition_row_sum (t u : ℕ) (i : Fin (2*t+1)) :
    2*(∑ j : Fin (2*u+3), ((partitionEquiv t u (i,j)).val+1)) =
      (2*u+3)*((2*t+1)*(2*u+3)+1) := by
  have he (j : Fin (2*u+3)) :
      (partitionEquiv t u (i,j)).val+1 = padNat t u i (padRoleEquiv u j) := by
    have hb := pad_bounds t u i (padRoleEquiv u j)
    change padNat t u i (padRoleEquiv u j)-1+1 = _
    omega
  simp_rw [he]
  rw [(padRoleEquiv u).sum_comp]
  simpa only [Nat.mul_comm (2*t+1) (2*u+3)] using pad_row_sum t u i

theorem partition_translated (t u a : ℕ) (i : Fin (2*t+1)) :
    2*(∑ j : Fin (2*u+3), (a+(partitionEquiv t u (i,j)).val)) =
      (2*u+3)*(2*a+(2*t+1)*(2*u+3)-1) := by
  have h := partition_row_sum t u i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one] at h ⊢
  have hd : (2*a+(2*t+1)*(2*u+3)-1)+1 = 2*a+(2*t+1)*(2*u+3) := by
    have hp : 0 < (2*t+1)*(2*u+3) := Nat.mul_pos (by omega) (by omega)
    omega
  have hm := congrArg (fun n => (2*u+3)*n) hd
  nlinarith [hm]

theorem odd_interval_partition (h s a : ℕ) (_hh : 0 < h) (ho : Odd h)
    (hs : 3 ≤ s) (so : Odd s) :
    ∃ f : (Fin h × Fin s) ≃ Fin (h*s),
      ∀ i, 2*(∑ j, (a+(f (i,j)).val)) = s*(2*a+h*s-1) := by
  obtain ⟨t,ht⟩ := ho
  obtain ⟨v,hv⟩ := so
  have hh' : h = 2*t+1 := by omega
  have hs' : s = 2*(v-1)+3 := by omega
  rw [hh', hs']
  exact ⟨partitionEquiv t (v-1), partition_translated t (v-1) a⟩

#print axioms partitionEquiv
#print axioms odd_interval_partition
end RFB
```

### `RFBFinish.lean`

```lean
import RFBExceptions
import RFBPoolProperties
import RFBPartition

namespace RFB

def SmallRange (r s : ℕ) : Prop :=
  (r = 2 ∧ 13 ≤ s) ∨ (r = 4 ∧ 9 ≤ s) ∨ (r = 6 ∧ 7 ≤ s)

def Exceptional (r s : ℕ) : Prop :=
  (r = 2 ∧ s = 3) ∨ (r = 2 ∧ s = 5) ∨ (r = 2 ∧ s = 7) ∨
  (r = 2 ∧ s = 9) ∨ (r = 2 ∧ s = 11) ∨ (r = 4 ∧ s = 3) ∨
  (r = 4 ∧ s = 5) ∨ (r = 4 ∧ s = 7) ∨ (r = 6 ∧ s = 3) ∨ (r = 6 ∧ s = 5)

theorem parameters_cover (r s : ℕ) (hr : 2 ≤ r) (hre : Even r)
    (hs : 3 ≤ s) (hso : Odd s) : 8 ≤ r ∨ SmallRange r s ∨ Exceptional r s := by
  obtain ⟨a,ha⟩ := hre
  obtain ⟨b,hb⟩ := hso
  unfold SmallRange Exceptional
  omega

def ThreeWitness (r s : ℕ) : Prop :=
  ∃ L : Labeling r s, IsLocalAntimagic (rFB r s) L.labelEquiv ∧
    colorCount (rFB r s) L.labelEquiv = 3

/-- Closure helper only. The two grouping hypotheses are the remaining tasks;
this is not an unconditional proof of Conjecture 5.1. -/
theorem finish_of_groupings
    (large : ∀ r s : ℕ, 8 ≤ r → Even r → 3 ≤ s → Odd s → ThreeWitness r s)
    (small : ∀ r s : ℕ, SmallRange r s → Odd s → ThreeWitness r s)
    (r s : ℕ) (hr : 2 ≤ r) (hre : Even r) (hs : 3 ≤ s) (hso : Odd s) :
    chiLA (rFB r s) = 3 := by
  obtain h | h | h := parameters_cover r s hr hre hs hso
  · obtain ⟨L,hp,hc⟩ := large r s h hre hs hso
    exact chiLA_of_witness r s (by omega) (by omega) L.labelEquiv hp hc
  · obtain ⟨L,hp,hc⟩ := small r s h hso
    exact chiLA_of_witness r s (by omega) (by omega) L.labelEquiv hp hc
  · exact exceptional_cases r s h

#print axioms parameters_cover
#print axioms finish_of_groupings
#print chiLA
#eval Lean.versionString
end RFB
```

### `RFBCanonical.lean`

```lean
import RFBPoolProperties
import RFBRoles
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RFB
set_option linter.unusedSimpArgs false

/-- Canonical positions: the 21 traded blades, then increasing ordinary centres. -/
noncomputable def canonicalColumn (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) : Fin (2*k) :=
  if h : i.val < 21 then removedColumn k hk ⟨i.val,h⟩
  else ((centreEquiv k hk).symm ⟨i.val-21, by have := i.isLt; omega⟩).val

theorem canonicalColumn_injective (k : ℕ) (hk : 11 ≤ k) :
    Function.Injective (canonicalColumn k hk) := by
  intro a b hab
  unfold canonicalColumn at hab
  split_ifs at hab with ha hb hb
  · have he := congrArg Fin.val hab
    have ha' := removedIndex_bounds k hk ⟨a.val,ha⟩
    have hb' := removedIndex_bounds k hk ⟨b.val,hb⟩
    change removedIndex k ⟨a.val,ha⟩ - 1 = removedIndex k ⟨b.val,hb⟩ - 1 at he
    have he' : removedIndex k ⟨a.val,ha⟩ = removedIndex k ⟨b.val,hb⟩ := by omega
    exact Fin.ext (congrArg (fun x : Fin 21 => x.val) (removedIndex_injective k hk he'))
  · have hh := ((centreEquiv k hk).symm ⟨b.val-21, by have := b.isLt; omega⟩).property
    have hv := congrArg Fin.val hab
    have hr := removedIndex_bounds k hk ⟨a.val,ha⟩
    exact False.elim (hh ⟨a.val,ha⟩ (by dsimp [removedColumn] at hv; omega))
  · have hh := ((centreEquiv k hk).symm ⟨a.val-21, by have := a.isLt; omega⟩).property
    have hv := congrArg Fin.val hab
    have hr := removedIndex_bounds k hk ⟨b.val,hb⟩
    exact False.elim (hh ⟨b.val,hb⟩ (by dsimp [removedColumn] at hv; omega))
  · have he : (centreEquiv k hk).symm ⟨a.val-21, by have := a.isLt; omega⟩ =
        (centreEquiv k hk).symm ⟨b.val-21, by have := b.isLt; omega⟩ := Subtype.ext hab
    have hv := congrArg Fin.val ((centreEquiv k hk).symm.injective he)
    exact Fin.ext (by dsimp at hv; omega)

noncomputable def canonicalEquiv (k : ℕ) (hk : 11 ≤ k) : Fin (2*k) ≃ Fin (2*k) :=
  Equiv.ofBijective (canonicalColumn k hk)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨canonicalColumn_injective k hk,rfl⟩)

noncomputable def canonicalBlade (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) : Fin 5 → ℕ :=
  poolBlade k hk (canonicalEquiv k hk i)

noncomputable def canonicalHub (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) : ℤ :=
  (canonicalBlade k hk i 0 : ℤ) + canonicalBlade k hk i 2 + canonicalBlade k hk i 4

theorem canonical_roles (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) :
    (canonicalBlade k hk i 0 + canonicalBlade k hk i 1 = 10*k+1 ∧
      canonicalBlade k hk i 3 + canonicalBlade k hk i 4 = 10*k+1 ∧
      canonicalBlade k hk i 1 + canonicalBlade k hk i 2 + canonicalBlade k hk i 3 = 13*k+1) ∨
    (canonicalBlade k hk i 0 + canonicalBlade k hk i 1 = 13*k+1 ∧
      canonicalBlade k hk i 3 + canonicalBlade k hk i 4 = 13*k+1 ∧
      canonicalBlade k hk i 1 + canonicalBlade k hk i 2 + canonicalBlade k hk i 3 = 10*k+1) := by
  by_cases h : i.val < 21
  · have ht := pool_trade_roles k hk ⟨i.val,h⟩
    change RoleEquations _ _ _ at ht
    unfold RoleEquations at ht
    simp only [canonicalBlade, canonicalEquiv, Equiv.ofBijective_apply, canonicalColumn, dite_eq_left h]
    dsimp only at ht
    split_ifs at ht <;> [right; left] <;> rcases ht with ⟨h1,h2,h3⟩ <;>
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  · left
    simpa only [canonicalBlade, canonicalEquiv, Equiv.ofBijective_apply, canonicalColumn, dite_eq_right h]
      using pool_ordinary k hk ((centreEquiv k hk).symm ⟨i.val-21, by have := i.isLt; omega⟩)

theorem canonical_ordinary_hub (k : ℕ) (hk : 11 ≤ k) (i : Fin (2*k)) (hi : 21 ≤ i.val) :
    canonicalHub k hk i = 7*(k : ℤ)+1+2*(4*k+10+(i.val:ℤ)-21) := by
  let c := (centreEquiv k hk).symm ⟨i.val-21, by have := i.isLt; omega⟩
  have hc := (kept_iff_centre_bounds k hk c.val).mp c.property
  have he := congrArg Fin.val ((centreEquiv k hk).apply_symm_apply ⟨i.val-21, by have := i.isLt; omega⟩)
  change supply k (c.val.val+1) 2 - (4*k+10) = i.val-21 at he
  have hcentre : (supply k (c.val.val+1) 2 : ℤ) = 4*k+10+(i.val:ℤ)-21 := by omega
  have hr := pool_ordinary k hk c
  have h1 : (poolBlade k hk c.val 0 : ℤ) + poolBlade k hk c.val 1 = 10*k+1 := by exact_mod_cast hr.1
  have h2 : (poolBlade k hk c.val 3 : ℤ) + poolBlade k hk c.val 4 = 10*k+1 := by exact_mod_cast hr.2.1
  have h3 : (poolBlade k hk c.val 1 : ℤ) + poolBlade k hk c.val 2 + poolBlade k hk c.val 3 = 13*k+1 := by exact_mod_cast hr.2.2
  have hv := pool_kept_value k hk c 2
  have hv' : (poolBlade k hk c.val 2 : ℤ) = 4*k+10+(i.val:ℤ)-21 := by rw [hv,hcentre]
  simp only [canonicalHub, canonicalBlade, canonicalEquiv, Equiv.ofBijective_apply,
    canonicalColumn, dite_eq_right (by omega : ¬i.val < 21)]
  change (poolBlade k hk c.val 0 : ℤ) + poolBlade k hk c.val 2 + poolBlade k hk c.val 4 = _
  linarith

theorem canonical_trade_hub (k : ℕ) (hk : 11 ≤ k) (g : Fin 7) :
    ∑ t : Fin 3, canonicalHub k hk ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩ =
      3*(17*(k : ℤ)-1) := by
  have he (t : Fin 3) : canonicalHub k hk ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩ =
      hub (fun a => (poolBlade k hk (removedColumn k hk ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩) a : ℤ)) := by
    simp only [canonicalHub, canonicalBlade, canonicalEquiv, Equiv.ofBijective_apply,
      canonicalColumn, dite_eq_left (by have := g.isLt; have := t.isLt; omega : 3*g.val+t.val < 21), hub]
  simp_rw [he]
  simpa only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero, add_assoc]
    using pool_trade_hub k hk g

#print axioms canonical_roles
#print axioms canonical_ordinary_hub
#print axioms canonical_trade_hub
end RFB
```

### `RFBSandwich.lean`

```lean
import RFBCanonical

namespace RFB
set_option linter.unusedSimpArgs false

/-- Reserve initial seeds, complementary outer pairs, and a central interval. -/
def sandwich (a p m n : ℕ) (hn : n = a+2*p+m)
    (x : Fin a ⊕ ((Fin p × Fin 2) ⊕ Fin m)) : Fin n :=
  match x with
  | .inl t => ⟨t.val, by have := t.isLt; omega⟩
  | .inr (.inl (q,b)) =>
    ⟨a+(if b.val = 0 then q.val else 2*p+m-1-q.val), by
      have := q.isLt; split_ifs <;> omega⟩
  | .inr (.inr z) => ⟨a+p+z.val, by have := z.isLt; omega⟩

theorem sandwich_injective (a p m n : ℕ) (hn : n = a+2*p+m) :
    Function.Injective (sandwich a p m n hn) := by
  intro x y h
  rcases x with t | (⟨q,b⟩ | z) <;> rcases y with t' | (⟨q',b'⟩ | z')
  · have hv := congrArg (fun x : Fin n => x.val) h
    exact congrArg Sum.inl (Fin.ext hv)
  · have ht := t.isLt
    have hq := q'.isLt
    have hv := congrArg Fin.val h
    change t.val = a+(if b'.val = 0 then q'.val else 2*p+m-1-q'.val) at hv
    split_ifs at hv <;> omega
  · have ht := t.isLt
    have hv := congrArg Fin.val h
    change t.val = a+p+z'.val at hv
    omega
  · have ht := t'.isLt
    have hq := q.isLt
    have hv := congrArg Fin.val h
    change a+(if b.val = 0 then q.val else 2*p+m-1-q.val) = t'.val at hv
    split_ifs at hv <;> omega
  · have hq := q.isLt
    have hq' := q'.isLt
    have hb := b.isLt
    have hb' := b'.isLt
    have hv := congrArg Fin.val h
    change a+(if b.val = 0 then q.val else 2*p+m-1-q.val) =
      a+(if b'.val = 0 then q'.val else 2*p+m-1-q'.val) at hv
    split_ifs at hv <;> try omega
    all_goals
      have heq : q = q' := Fin.ext (by omega)
      have heb : b = b' := Fin.ext (by omega)
      rw [heq,heb]
  · have hq := q.isLt
    have hz := z'.isLt
    have hv := congrArg Fin.val h
    change a+(if b.val = 0 then q.val else 2*p+m-1-q.val) = a+p+z'.val at hv
    split_ifs at hv <;> omega
  · have ht := t'.isLt
    have hv := congrArg Fin.val h
    change a+p+z.val = t'.val at hv
    omega
  · have hq := q'.isLt
    have hz := z.isLt
    have hv := congrArg Fin.val h
    change a+p+z.val = a+(if b'.val = 0 then q'.val else 2*p+m-1-q'.val) at hv
    split_ifs at hv <;> omega
  · have hv := congrArg Fin.val h
    change a+p+z.val = a+p+z'.val at hv
    exact congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext (by omega))

noncomputable def sandwichEquiv (a p m n : ℕ) (hn : n = a+2*p+m) :
    (Fin a ⊕ ((Fin p × Fin 2) ⊕ Fin m)) ≃ Fin n :=
  Equiv.ofBijective (sandwich a p m n hn)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨sandwich_injective a p m n hn, by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega⟩)

#print axioms sandwich_injective
end RFB
```

### `RFBLargeOrder.lean`

```lean
import RFBSandwich
import RFBPartition

namespace RFB
set_option linter.unusedSimpArgs false

noncomputable def largeSplit (h u : ℕ) :
    ((Fin 7 × PadRole u) ⊕ (Fin h × Fin (2*u+3))) ≃
      (Fin 21 ⊕ ((Fin (7*u) × Fin 2) ⊕ Fin (h*(2*u+3)))) :=
  (Equiv.sumCongr
    ((Equiv.prodSumDistrib (Fin 7) (Fin 3) (Fin u × Fin 2)).trans
      (Equiv.sumCongr finProdFinEquiv
        ((Equiv.prodAssoc (Fin 7) (Fin u) (Fin 2)).symm.trans
          (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)))))
    finProdFinEquiv).trans (Equiv.sumAssoc _ _ _)

/-- Replace the central interval's lexicographic order by the equal-sum order. -/
noncomputable def largeSlots (h u : ℕ)
    (f : (Fin h × Fin (2*u+3)) ≃ Fin (h*(2*u+3))) :
    (((Fin 7 ⊕ Fin h) × Fin (2*u+3))) ≃
      (Fin 21 ⊕ ((Fin (7*u) × Fin 2) ⊕ Fin (h*(2*u+3)))) :=
  ((Equiv.sumProdDistrib _ _ _).trans
    (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) (padRoleEquiv u))
      (Equiv.refl _))).trans
    ((Equiv.sumCongr (Equiv.refl _) (finProdFinEquiv.trans f.symm).symm).trans
      (largeSplit h u))

-- The explicit central reindexing above cancels the lexicographic equivalence.
theorem largeSlots_seed (h u : ℕ)
    (f : (Fin h × Fin (2*u+3)) ≃ Fin (h*(2*u+3)))
    (g : Fin 7) (j : Fin (2*u+3)) :
    largeSlots h u f (.inl g,j) =
      match padRoleEquiv u j with
      | .inl t => .inl (finProdFinEquiv (g,t))
      | .inr (q,b) => .inr (.inl (finProdFinEquiv (g,q),b)) := by
  cases he : padRoleEquiv u j with
  | inl t => simp [largeSlots,largeSplit,he]
  | inr qb => cases qb; simp [largeSlots,largeSplit,he]

theorem largeSlots_central (h u : ℕ)
    (f : (Fin h × Fin (2*u+3)) ≃ Fin (h*(2*u+3)))
    (i : Fin h) (j : Fin (2*u+3)) :
    largeSlots h u f (.inr i,j) = .inr (.inr (f (i,j))) := by
  simp [largeSlots,largeSplit]
  exact finProdFinEquiv.apply_symm_apply (f (i,j))

#print axioms largeSlots
end RFB
```

### `RFBAssemblyBridge.lean`

```lean
import RFBCanonical
import RFBFinish

namespace RFB
set_option linter.unusedSimpArgs false

/-- An equal-hub permutation of canonical blades gives the literal three-colour witness. -/
theorem witness_of_canonical (r s k : ℕ) (hr : 0 < r) (hs : 3 ≤ s)
    (hk : 11 ≤ k) (hrs : r*s = 2*k)
    (order : (Fin r × Fin s) ≃ Fin (2*k))
    (hh : ∀ i, ∑ j : Fin s, canonicalHub k hk (order (i,j)) = s*(17*(k:ℤ)-1)) :
    ThreeWitness r s := by
  let L := assembledLabeling r s k hk (by nlinarith [hrs]) (order.trans (canonicalEquiv k hk))
  have hv (i : Fin r) (j : Fin s) (t : Fin 5) :
      L.label (i,j,t) = canonicalBlade k hk (order (i,j)) t := rfl
  have hb : BladeRoles L.label (10*k+1) (13*k+1) := by
    intro i j
    simpa only [hv] using canonical_roles k hk (order (i,j))
  have hj : (17*k-1:ℕ) = 17*k-1 := rfl
  have hj' : ((17*k-1:ℕ):ℤ) = 17*(k:ℤ)-1 := by omega
  have hH : HubSums L.label (s*(17*k-1)) := by
    intro i
    have h := hh i
    simp only [canonicalHub, ← Nat.cast_add, ← Nat.cast_sum, ← hv] at h
    have hcast : ((s*(17*k-1):ℕ):ℤ) = s*(17*(k:ℤ)-1) := by rw [Nat.cast_mul,hj']
    rw [← hcast] at h
    exact_mod_cast h
  have hAB : 10*k+1 ≠ 13*k+1 := by omega
  have hbig : 13*k+1 < s*(17*k-1) := by
    have h1 : 13*k+1 < 3*(17*k-1) := by omega
    exact h1.trans_le (Nat.mul_le_mul_right _ hs)
  have hp := roles_proper L.label hb hH hAB (by omega) (by omega)
  have hf : IsLocalAntimagic (rFB r s) L.labelEquiv := by
    apply proper_transfer
    simpa only [indexedSum_eq_roleSum] using hp
  refine ⟨L,hf, Nat.le_antisymm ?_ (triangle_lower r s hr (by omega) _ hf)⟩
  rw [colorCount_transfer]
  have heq : indexedSum L.label = roleSum L.label := funext (indexedSum_eq_roleSum L.label)
  rw [heq]
  exact roles_count_le L.label hb hH

#print axioms witness_of_canonical
end RFB
```

### `RFBSandwichSums.lean`

```lean
import RFBSandwich

namespace RFB
set_option linter.unusedSimpArgs false

theorem sandwich_pair_hub (k p m : ℕ) (hk : 11 ≤ k)
    (hn : 2*k = 21+2*p+m) (q : Fin p) :
    (∑ b : Fin 2, canonicalHub k hk (sandwich 21 p m (2*k) hn (.inr (.inl (q,b))))) =
      2*(17*(k:ℤ)-1) := by
  have hq := q.isLt
  have h0 : 21 ≤ (sandwich 21 p m (2*k) hn (.inr (.inl (q,0)))).val := by simp [sandwich]
  have h1 : 21 ≤ (sandwich 21 p m (2*k) hn (.inr (.inl (q,1)))).val := by simp [sandwich]
  rw [Fin.sum_univ_two, canonical_ordinary_hub k hk _ h0, canonical_ordinary_hub k hk _ h1]
  simp only [sandwich, Fin.val_zero, Fin.val_one, ite_true, ite_false, Fin.val_mk]
  have hsub : ((2*p+m-1-q.val:ℕ):ℤ) = 2*(p:ℤ)+m-1-q.val := by omega
  push_cast
  rw [hsub]
  have hn' : 2*(k:ℤ) = 21+2*p+m := by exact_mod_cast hn
  linarith

theorem sandwich_seed_hub (k p m : ℕ) (hk : 11 ≤ k)
    (hn : 2*k = 21+2*p+m) (g : Fin 7) :
    (∑ t : Fin 3, canonicalHub k hk (sandwich 21 p m (2*k) hn
      (.inl (finProdFinEquiv (g,t))))) = 3*(17*(k:ℤ)-1) := by
  have he (t : Fin 3) : sandwich 21 p m (2*k) hn (.inl (finProdFinEquiv (g,t))) =
      ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩ := by
    apply Fin.ext
    simp only [sandwich,finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_mk]
    omega
  simp_rw [he]
  exact canonical_trade_hub k hk g

#print axioms sandwich_pair_hub
#print axioms sandwich_seed_hub
end RFB
```

### `RFBLargeAssembly.lean`

```lean
import RFBLargeOrder
import RFBSandwichSums
import RFBAssemblyBridge

namespace RFB
set_option linter.unusedSimpArgs false

theorem large_slots_sum (h u k : ℕ) (hk : 11 ≤ k)
    (hn : 2*k = 21+2*(7*u)+h*(2*u+3))
    (f : (Fin h × Fin (2*u+3)) ≃ Fin (h*(2*u+3)))
    (hf : ∀ i, 2*(∑ j, (4*k+10+7*u+(f (i,j)).val)) =
      (2*u+3)*(2*(4*k+10+7*u)+h*(2*u+3)-1))
    (i : Fin 7 ⊕ Fin h) :
    ∑ j : Fin (2*u+3), canonicalHub k hk
      (sandwichEquiv 21 (7*u) (h*(2*u+3)) (2*k) hn (largeSlots h u f (i,j))) =
      (2*u+3)*(17*(k:ℤ)-1) := by
  cases i with
  | inl g =>
    simp_rw [largeSlots_seed]
    let F : PadRole u → ℤ := fun x => canonicalHub k hk
      (sandwich 21 (7*u) (h*(2*u+3)) (2*k) hn
        (match x with
         | .inl t => .inl (finProdFinEquiv (g,t))
         | .inr (q,b) => .inr (.inl (finProdFinEquiv (g,q),b))))
    change (∑ j, F (padRoleEquiv u j)) = _
    rw [(padRoleEquiv u).sum_comp, Fintype.sum_sum_type]
    change (∑ t : Fin 3, canonicalHub k hk (sandwich 21 (7*u) (h*(2*u+3)) (2*k) hn
      (.inl (finProdFinEquiv (g,t))))) +
      (∑ qb : Fin u × Fin 2, canonicalHub k hk (sandwich 21 (7*u) (h*(2*u+3)) (2*k) hn
        (.inr (.inl (finProdFinEquiv (g,qb.1),qb.2))))) = _
    rw [sandwich_seed_hub, Fintype.sum_prod_type]
    simp_rw [sandwich_pair_hub]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  | inr i =>
    simp_rw [largeSlots_central]
    have he (j : Fin (2*u+3)) : canonicalHub k hk
        (sandwichEquiv 21 (7*u) (h*(2*u+3)) (2*k) hn (.inr (.inr (f (i,j))))) =
        7*(k:ℤ)+1+2*(4*k+10+7*u+((f (i,j)).val:ℤ)) := by
      rw [canonical_ordinary_hub k hk _ (by
        change 21 ≤ 21+7*u+(f (i,j)).val; omega)]
      change 7*(k:ℤ)+1+2*(4*k+10+((21+7*u+(f (i,j)).val:ℕ):ℤ)-21) = _
      push_cast
      ring
    simp_rw [he]
    have hf' : 2*(∑ j : Fin (2*u+3), ((4*k+10+7*u+(f (i,j)).val:ℕ):ℤ)) =
        ((2*u+3:ℕ):ℤ)*((2*(4*k+10+7*u)+h*(2*u+3)-1:ℕ):ℤ) := by exact_mod_cast hf i
    have hsub : ((2*(4*k+10+7*u)+h*(2*u+3)-1:ℕ):ℤ) =
        2*(4*(k:ℤ)+10+7*u)+h*(2*u+3)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*(4*k+10+7*u)+h*(2*u+3))]
      push_cast
      ring
    rw [hsub] at hf'
    push_cast at hf'
    have hn' : 2*(k:ℤ) = 21+2*(7*u)+h*(2*u+3) := by exact_mod_cast hn
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hf'
    push_cast at hf'
    have hm := congrArg (fun z : ℤ => (2*(u:ℤ)+3)*z) hn'
    nlinarith [hf',hm]

theorem large_assembly (r s : ℕ) (hr : 8 ≤ r) (hre : Even r)
    (hs : 3 ≤ s) (hso : Odd s) : ThreeWitness r s := by
  obtain ⟨a,ha⟩ := hre
  obtain ⟨b,hb⟩ := hso
  let h := r-7
  let u := b-1
  let k := a*s
  have hs' : s = 2*u+3 := by dsimp [u]; omega
  have hh : 0 < h := by dsimp [h]; omega
  have hho : Odd h := by
    refine ⟨a-4,?_⟩
    dsimp [h]
    omega
  have hrs : r*s = 2*k := by dsimp [k]; nlinarith [ha]
  have hk : 11 ≤ k := by dsimp [k]; nlinarith
  have hn : 2*k = 21+2*(7*u)+h*(2*u+3) := by
    have hh' : h+7 = r := by dsimp [h]; omega
    have hrs' : r*(2*u+3) = 2*k := by rw [← hs']; exact hrs
    nlinarith [hrs']
  obtain ⟨f,hf⟩ := odd_interval_partition h (2*u+3) (4*k+10+7*u) hh hho
    (by omega) (by exact ⟨u+1, by omega⟩)
  let rows : Fin r ≃ (Fin 7 ⊕ Fin h) :=
    (finCongr (by dsimp [h]; omega : r = 7+h)).trans finSumFinEquiv.symm
  let order : (Fin r × Fin s) ≃ Fin (2*k) :=
    ((Equiv.prodCongr rows (finCongr hs')).trans (largeSlots h u f)).trans
      (sandwichEquiv 21 (7*u) (h*(2*u+3)) (2*k) hn)
  apply witness_of_canonical r s k (by omega) hs hk hrs order
  intro i
  have he (j : Fin s) : order (i,j) = sandwichEquiv 21 (7*u) (h*(2*u+3)) (2*k) hn
      (largeSlots h u f (rows i,finCongr hs' j)) := rfl
  simp_rw [he]
  rw [(finCongr hs').sum_comp (fun j => canonicalHub k hk
    (sandwichEquiv 21 (7*u) (h*(2*u+3)) (2*k) hn (largeSlots h u f (rows i,j))))]
  simpa only [hs', Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    large_slots_sum h u k hk hn f hf (rows i)

#print axioms large_assembly
end RFB
```

### `RFBSmallPool.lean`

```lean
import RFBCanonical

namespace RFB
set_option linter.unusedSimpArgs false

/-- The median ordinary blade is the twenty-second seed. -/
def smallPool (k : ℕ) (hk : 11 ≤ k) (x : Fin 22 ⊕ (Fin (k-11) × Fin 2)) : Fin (2*k) :=
  match x with
  | .inl t => ⟨if t.val < 21 then t.val else k+10, by split_ifs <;> omega⟩
  | .inr (q,b) => ⟨if b.val = 0 then 21+q.val else 2*k-1-q.val, by
      have := q.isLt; split_ifs <;> omega⟩

theorem smallPool_injective (k : ℕ) (hk : 11 ≤ k) : Function.Injective (smallPool k hk) := by
  intro x y h
  rcases x with t | ⟨q,b⟩ <;> rcases y with t' | ⟨q',b'⟩
  · have ht := t.isLt
    have ht' := t'.isLt
    have hv := congrArg Fin.val h
    change (if t.val < 21 then t.val else k+10) = (if t'.val < 21 then t'.val else k+10) at hv
    split_ifs at hv <;> try omega
    all_goals exact congrArg Sum.inl (Fin.ext (by omega))
  · have ht := t.isLt
    have hq := q'.isLt
    have hv := congrArg Fin.val h
    change (if t.val < 21 then t.val else k+10) =
      (if b'.val = 0 then 21+q'.val else 2*k-1-q'.val) at hv
    split_ifs at hv <;> omega
  · have ht := t'.isLt
    have hq := q.isLt
    have hv := congrArg Fin.val h
    change (if b.val = 0 then 21+q.val else 2*k-1-q.val) =
      (if t'.val < 21 then t'.val else k+10) at hv
    split_ifs at hv <;> omega
  · have hq := q.isLt
    have hq' := q'.isLt
    have hb := b.isLt
    have hb' := b'.isLt
    have hv := congrArg Fin.val h
    change (if b.val = 0 then 21+q.val else 2*k-1-q.val) =
      (if b'.val = 0 then 21+q'.val else 2*k-1-q'.val) at hv
    split_ifs at hv <;> try omega
    all_goals
      have heq : q = q' := Fin.ext (by omega)
      have heb : b = b' := Fin.ext (by omega)
      rw [heq,heb]

noncomputable def smallPoolEquiv (k : ℕ) (hk : 11 ≤ k) :
    (Fin 22 ⊕ (Fin (k-11) × Fin 2)) ≃ Fin (2*k) :=
  Equiv.ofBijective (smallPool k hk)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨smallPool_injective k hk, by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega⟩)

noncomputable def smallSeedHub (k : ℕ) (hk : 11 ≤ k) (t : Fin 22) : ℤ :=
  canonicalHub k hk (smallPool k hk (.inl t))

theorem smallSeed_triple (k : ℕ) (hk : 11 ≤ k) (g : Fin 7) :
    smallSeedHub k hk ⟨3*g.val, by omega⟩ +
    smallSeedHub k hk ⟨3*g.val+1, by omega⟩ +
    smallSeedHub k hk ⟨3*g.val+2, by omega⟩ = 3*(17*(k:ℤ)-1) := by
  have he (t : Fin 3) : canonicalHub k hk ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩ =
      smallSeedHub k hk ⟨3*g.val+t.val, by have := g.isLt; have := t.isLt; omega⟩ := by
    simp only [smallSeedHub,smallPool,ite_true, show 3*g.val+t.val < 21 by have := g.isLt; have := t.isLt; omega]
  have ht := canonical_trade_hub k hk g
  simp_rw [he] at ht
  simpa only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero, add_assoc] using ht

theorem smallSeed_median (k : ℕ) (hk : 11 ≤ k) : smallSeedHub k hk 21 = 17*(k:ℤ)-1 := by
  change canonicalHub k hk ⟨k+10, by omega⟩ = _
  rw [canonical_ordinary_hub k hk _ (by change 21 ≤ k+10; omega)]
  push_cast
  ring

theorem smallPool_pair_hub (k : ℕ) (hk : 11 ≤ k) (q : Fin (k-11)) :
    (∑ b : Fin 2, canonicalHub k hk (smallPool k hk (.inr (q,b)))) = 2*(17*(k:ℤ)-1) := by
  have hq := q.isLt
  rw [Fin.sum_univ_two]
  rw [canonical_ordinary_hub k hk _ (by change 21 ≤ 21+q.val; omega)]
  rw [canonical_ordinary_hub k hk _ (by change 21 ≤ 2*k-1-q.val; omega)]
  change 7*(k:ℤ)+1+2*(4*k+10+((21+q.val:ℕ):ℤ)-21) +
    (7*(k:ℤ)+1+2*(4*k+10+((2*k-1-q.val:ℕ):ℤ)-21)) = _
  have he : ((2*k-1-q.val:ℕ):ℤ) = 2*(k:ℤ)-1-q.val := by omega
  rw [he]
  push_cast
  ring

#print axioms smallPool_injective
#print axioms smallSeed_triple
#print axioms smallSeed_median
#print axioms smallPool_pair_hub
end RFB
```

### `RFBSmallGrouping.lean`

```lean
import RFBSmallPool
import RFBAssemblyBridge

namespace RFB
set_option linter.unusedSimpArgs false

noncomputable def smallSlots {r s k : ℕ} (d q : Fin r → ℕ)
    (rows : ∀ i, Fin s ≃ (Fin (d i) ⊕ (Fin (q i) × Fin 2)))
    (seeds : (Σ i, Fin (d i)) ≃ Fin 22)
    (pairs : (Σ i, Fin (q i)) ≃ Fin (k-11)) :
    (Fin r × Fin s) ≃ (Fin 22 ⊕ (Fin (k-11) × Fin 2)) :=
  ((Equiv.sigmaEquivProd _ _).symm.trans (Equiv.sigmaCongrRight rows)).trans
    ((Equiv.sigmaSumDistrib _ _).trans
      (Equiv.sumCongr seeds
        ((Equiv.sigmaProdDistrib _ _).symm.trans
          (Equiv.prodCongr pairs (Equiv.refl _)))))

theorem small_grouping (r s k : ℕ) (hr : 0 < r) (hs : 3 ≤ s)
    (hk : 11 ≤ k) (hrs : r*s = 2*k)
    (d q : Fin r → ℕ) (hdq : ∀ i, d i+2*q i = s)
    (seeds : (Σ i, Fin (d i)) ≃ Fin 22)
    (hseeds : ∀ i, (∑ t : Fin (d i), smallSeedHub k hk (seeds ⟨i,t⟩)) =
      d i*(17*(k:ℤ)-1)) : ThreeWitness r s := by
  have hdsum : ∑ i, d i = 22 := by
    have hc := Fintype.card_congr seeds
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hc
  have hqsum : ∑ i, q i = k-11 := by
    have ht : ∑ i, (d i+2*q i) = ∑ _i : Fin r, s := Finset.sum_congr rfl (fun i _ => hdq i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hrs] at ht
    omega
  let pairs : (Σ i, Fin (q i)) ≃ Fin (k-11) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma,Fintype.card_fin]; exact hqsum)
  let rows (i : Fin r) : Fin s ≃ (Fin (d i) ⊕ (Fin (q i) × Fin 2)) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; have := hdq i; omega)
  let slots := smallSlots d q rows seeds pairs
  let order := slots.trans (smallPoolEquiv k hk)
  apply witness_of_canonical r s k hr hs hk hrs order
  intro i
  let F : (Fin (d i) ⊕ (Fin (q i) × Fin 2)) → ℤ := fun x =>
    match x with
    | .inl t => smallSeedHub k hk (seeds ⟨i,t⟩)
    | .inr (a,b) => canonicalHub k hk (smallPool k hk (.inr (pairs ⟨i,a⟩,b)))
  have he (j : Fin s) : canonicalHub k hk (order (i,j)) = F (rows i j) := by
    cases hj : rows i j with
    | inl t => simp [order,slots,smallSlots,F,hj,smallSeedHub,smallPoolEquiv]
    | inr ab => cases ab; simp [order,slots,smallSlots,F,hj,smallPoolEquiv]
  simp_rw [he]
  rw [(rows i).sum_comp,Fintype.sum_sum_type]
  change (∑ t : Fin (d i), smallSeedHub k hk (seeds ⟨i,t⟩)) +
    (∑ ab : Fin (q i) × Fin 2, canonicalHub k hk
      (smallPool k hk (.inr (pairs ⟨i,ab.1⟩,ab.2)))) = _
  rw [hseeds,Fintype.sum_prod_type]
  simp_rw [smallPool_pair_hub]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have ht : (d i:ℤ)+2*q i = s := by exact_mod_cast hdq i
  nlinarith

#print axioms small_grouping
end RFB
```

### `RFBPlan2.lean`

```lean
import RFBSmallGrouping

namespace RFB
namespace Plan2
set_option linter.unusedSimpArgs false

def sizes : Fin 2 → ℕ := ![9,13]
def starts : Fin 2 → ℕ := ![0,9]

def seedMap (x : Σ i, Fin (sizes i)) : Fin 22 :=
  ⟨starts x.1+x.2.val, by
    rcases x with ⟨i,t⟩
    have := t.isLt
    fin_cases i <;> simp_all [sizes,starts] <;> omega⟩

theorem seedMap_injective : Function.Injective seedMap := by decide

noncomputable def seeds : (Σ i, Fin (sizes i)) ≃ Fin 22 :=
  Equiv.ofBijective seedMap
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨seedMap_injective, by decide⟩)

theorem seed_sums (k : ℕ) (hk : 11 ≤ k) (i : Fin 2) :
    (∑ t : Fin (sizes i), smallSeedHub k hk (seeds ⟨i,t⟩)) = sizes i*(17*(k:ℤ)-1) := by
  have h0 := smallSeed_triple k hk 0
  have h1 := smallSeed_triple k hk 1
  have h2 := smallSeed_triple k hk 2
  have h3 := smallSeed_triple k hk 3
  have h4 := smallSeed_triple k hk 4
  have h5 := smallSeed_triple k hk 5
  have h6 := smallSeed_triple k hk 6
  have hm := smallSeed_median k hk
  norm_num at h0 h1 h2 h3 h4 h5 h6
  fin_cases i
  · change (∑ t : Fin 9, smallSeedHub k hk ⟨0+t.val, by have := t.isLt; omega⟩) = 9*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 13, smallSeedHub k hk ⟨9+t.val, by have := t.isLt; omega⟩) = 13*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega

theorem witness (s : ℕ) (hs : 13 ≤ s) (ho : Odd s) : ThreeWitness 2 s := by
  obtain ⟨b,hb⟩ := ho
  let k := 1*s
  have hk : 11 ≤ k := by dsimp [k]; omega
  have hrs : 2*s = 2*k := by dsimp [k]; omega
  apply small_grouping 2 s k (by decide) (by omega) hk hrs sizes (fun i => (s-sizes i)/2)
    (fun i => ?_) seeds (seed_sums k hk)
  fin_cases i <;> norm_num [sizes] <;> omega

#print axioms witness
end Plan2
end RFB
```

### `RFBPlan4.lean`

```lean
import RFBSmallGrouping

namespace RFB
namespace Plan4
set_option linter.unusedSimpArgs false

def sizes : Fin 4 → ℕ := ![3,3,9,7]
def starts : Fin 4 → ℕ := ![0,3,6,15]

def seedMap (x : Σ i, Fin (sizes i)) : Fin 22 :=
  ⟨starts x.1+x.2.val, by
    rcases x with ⟨i,t⟩
    have := t.isLt
    fin_cases i <;> simp_all [sizes,starts] <;> omega⟩

theorem seedMap_injective : Function.Injective seedMap := by decide

noncomputable def seeds : (Σ i, Fin (sizes i)) ≃ Fin 22 :=
  Equiv.ofBijective seedMap
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨seedMap_injective, by decide⟩)

theorem seed_sums (k : ℕ) (hk : 11 ≤ k) (i : Fin 4) :
    (∑ t : Fin (sizes i), smallSeedHub k hk (seeds ⟨i,t⟩)) = sizes i*(17*(k:ℤ)-1) := by
  have h0 := smallSeed_triple k hk 0
  have h1 := smallSeed_triple k hk 1
  have h2 := smallSeed_triple k hk 2
  have h3 := smallSeed_triple k hk 3
  have h4 := smallSeed_triple k hk 4
  have h5 := smallSeed_triple k hk 5
  have h6 := smallSeed_triple k hk 6
  have hm := smallSeed_median k hk
  norm_num at h0 h1 h2 h3 h4 h5 h6
  fin_cases i
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨0+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨3+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 9, smallSeedHub k hk ⟨6+t.val, by have := t.isLt; omega⟩) = 9*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 7, smallSeedHub k hk ⟨15+t.val, by have := t.isLt; omega⟩) = 7*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega

theorem witness (s : ℕ) (hs : 9 ≤ s) (ho : Odd s) : ThreeWitness 4 s := by
  obtain ⟨b,hb⟩ := ho
  let k := 2*s
  have hk : 11 ≤ k := by dsimp [k]; omega
  have hrs : 4*s = 2*k := by dsimp [k]; omega
  apply small_grouping 4 s k (by decide) (by omega) hk hrs sizes (fun i => (s-sizes i)/2)
    (fun i => ?_) seeds (seed_sums k hk)
  fin_cases i <;> norm_num [sizes] <;> omega

#print axioms witness
end Plan4
end RFB
```

### `RFBPlan6.lean`

```lean
import RFBSmallGrouping

namespace RFB
namespace Plan6
set_option linter.unusedSimpArgs false

def sizes : Fin 6 → ℕ := ![3,3,3,3,3,7]
def starts : Fin 6 → ℕ := ![0,3,6,9,12,15]

def seedMap (x : Σ i, Fin (sizes i)) : Fin 22 :=
  ⟨starts x.1+x.2.val, by
    rcases x with ⟨i,t⟩
    have := t.isLt
    fin_cases i <;> simp_all [sizes,starts] <;> omega⟩

theorem seedMap_injective : Function.Injective seedMap := by decide

noncomputable def seeds : (Σ i, Fin (sizes i)) ≃ Fin 22 :=
  Equiv.ofBijective seedMap
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨seedMap_injective, by decide⟩)

theorem seed_sums (k : ℕ) (hk : 11 ≤ k) (i : Fin 6) :
    (∑ t : Fin (sizes i), smallSeedHub k hk (seeds ⟨i,t⟩)) = sizes i*(17*(k:ℤ)-1) := by
  have h0 := smallSeed_triple k hk 0
  have h1 := smallSeed_triple k hk 1
  have h2 := smallSeed_triple k hk 2
  have h3 := smallSeed_triple k hk 3
  have h4 := smallSeed_triple k hk 4
  have h5 := smallSeed_triple k hk 5
  have h6 := smallSeed_triple k hk 6
  have hm := smallSeed_median k hk
  norm_num at h0 h1 h2 h3 h4 h5 h6
  fin_cases i
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨0+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨3+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨6+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨9+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 3, smallSeedHub k hk ⟨12+t.val, by have := t.isLt; omega⟩) = 3*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega
  · change (∑ t : Fin 7, smallSeedHub k hk ⟨15+t.val, by have := t.isLt; omega⟩) = 7*(17*(k:ℤ)-1)
    simp only [Fin.sum_univ_succ]
    norm_num
    omega

theorem witness (s : ℕ) (hs : 7 ≤ s) (ho : Odd s) : ThreeWitness 6 s := by
  obtain ⟨b,hb⟩ := ho
  let k := 3*s
  have hk : 11 ≤ k := by dsimp [k]; omega
  have hrs : 6*s = 2*k := by dsimp [k]; omega
  apply small_grouping 6 s k (by decide) (by omega) hk hrs sizes (fun i => (s-sizes i)/2)
    (fun i => ?_) seeds (seed_sums k hk)
  fin_cases i <;> norm_num [sizes] <;> omega

#print axioms witness
end Plan6
end RFB
```

### `RFBConjecture.lean`

```lean
import RFBLargeAssembly
import RFBPlan2
import RFBPlan4
import RFBPlan6

namespace RFB

theorem small_r_assembly (r s : ℕ)
    (h : (r = 2 ∧ 13 ≤ s) ∨ (r = 4 ∧ 9 ≤ s) ∨ (r = 6 ∧ 7 ≤ s))
    (hso : Odd s) : ThreeWitness r s := by
  rcases h with ⟨rfl,hs⟩ | ⟨rfl,hs⟩ | ⟨rfl,hs⟩
  · exact Plan2.witness s hs hso
  · exact Plan4.witness s hs hso
  · exact Plan6.witness s hs hso

/-- Conjecture 5.1 of Lau–Shiu–Nalliah–Premalatha, for the literal graph. -/
theorem conj_5_1 (r s : ℕ) (hr : 2 ≤ r) (hre : Even r)
    (hs : 3 ≤ s) (hso : Odd s) : chiLA (rFB r s) = 3 :=
  finish_of_groupings large_assembly small_r_assembly r s hr hre hs hso

/-- The minimum is attained by a bijection on the graph's actual edge set. -/
theorem conj_5_1_attained (r s : ℕ) (hr : 2 ≤ r) (hre : Even r)
    (hs : 3 ≤ s) (hso : Odd s) :
    ∃ f : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet),
      IsLocalAntimagic (rFB r s) f ∧ colorCount (rFB r s) f = 3 := by
  have hc := conj_5_1 r s hr hre hs hso
  have hn : {c | ∃ f : (rFB r s).edgeSet ≃ Fin (Fintype.card (rFB r s).edgeSet),
      IsLocalAntimagic (rFB r s) f ∧ colorCount (rFB r s) f = c}.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hz : chiLA (rFB r s) = 0 := by unfold chiLA; rw [he]; exact Nat.sInf_empty
    omega
  have hm := Nat.sInf_mem hn
  change ∃ f, IsLocalAntimagic (rFB r s) f ∧ colorCount (rFB r s) f = chiLA (rFB r s) at hm
  simpa only [hc] using hm

#print axioms large_assembly
#print axioms small_r_assembly
#print axioms conj_5_1
#print axioms conj_5_1_attained
#print conj_5_1
#print ThreeWitness
#print rFB
#print FBAdj
#print vsum
#print IsLocalAntimagic
#print colorCount
#print chiLA
#eval Lean.versionString
end RFB
```


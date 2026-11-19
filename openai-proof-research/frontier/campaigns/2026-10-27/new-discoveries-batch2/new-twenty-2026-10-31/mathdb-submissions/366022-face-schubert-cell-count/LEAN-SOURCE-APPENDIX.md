# MathDB 366022 Lean source appendix

The 23 canonical modules follow in dependency order. Each fenced block contains the exact source bytes, including its final newline.

## PinsProbe.lean

```lean
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

#eval Lean.versionString
#check convexHull_min
#check Convex.sum_mem
#check convexHull_pair
#check convex_Iic
#check Matrix.det_succ_row_zero
#check LinearEquiv.finrank_eq
#check continuous_apply
#check interior_maximal
```

## Geometry.lean

```lean
import PinsProbe

namespace G366022

abbrev R := Fin 4 → ℝ
noncomputable section

def gQ : Fin 8 → Fin 4 → ℚ :=
  ![![1,0,0,0], ![0,0,1,0], ![1/2,1/2,0,0], ![0,1/2,1/2,0],
    ![1/2,0,0,1/2], ![0,0,1/2,1/2], ![3/2,-1,3/2,-1], ![1/8,9/8,1/4,-1/2]]

def g (i : Fin 8) : R := fun j => (gQ i j : ℝ)

def coeff (w : R) : R →ₗ[ℝ] ℝ where
  toFun x := w 0 * x 0 + w 1 * x 1 + w 2 * x 2 + w 3 * x 3
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem coeff_apply (w x : R) :
    coeff w x = w 0 * x 0 + w 1 * x 1 + w 2 * x 2 + w 3 * x 3 := rfl

def h : R →ₗ[ℝ] ℝ := coeff ![1,1,1,1]

@[simp] theorem h_apply (x : R) : h x = x 0 + x 1 + x 2 + x 3 := by
  simp [h, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

def P : Set R := convexHull ℝ (Set.range g)
abbrev H := {x : R // h x = 1}
def PChart : Set H := Subtype.val ⁻¹' P

theorem g_mem (i : Fin 8) : g i ∈ P :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

theorem h_g (i : Fin 8) : h (g i) = 1 := by
  fin_cases i <;> norm_num [g, gQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem in_chart {x : R} (hx : x ∈ P) : h x = 1 := by
  suffices P ⊆ {y | h y = 1} from this hx
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    exact h_g i
  · intro u hu v hv a b _ _ hab
    change h u = 1 at hu
    change h v = 1 at hv
    change h (a • u + b • v) = 1
    simp only [map_add, map_smul, smul_eq_mul, hu, hv, mul_one, hab]

def face (K : Set R) (l : R →ₗ[ℝ] ℝ) (m : ℝ) : Set R :=
  {x ∈ K | l x = m}

theorem face_hull (S : Set R) (l : R →ₗ[ℝ] ℝ) (m : ℝ)
    (hu : ∀ x ∈ S, l x ≤ m) :
    face (convexHull ℝ S) l m = convexHull ℝ {x ∈ S | l x = m} := by
  let T := convexHull ℝ {x ∈ S | l x = m}
  have hT : convexHull ℝ S ⊆ {x | l x ≤ m ∧ (l x = m → x ∈ T)} := by
    apply convexHull_min
    · intro x hx
      exact ⟨hu x hx, fun hm => subset_convexHull ℝ _ ⟨hx,hm⟩⟩
    · intro u hu v hv a b ha hb hab
      change l u ≤ m ∧ (l u = m → u ∈ T) at hu
      change l v ≤ m ∧ (l v = m → v ∈ T) at hv
      change l (a • u + b • v) ≤ m ∧ (l (a • u + b • v) = m → _)
      simp only [map_add, map_smul, smul_eq_mul]
      have hid : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
      refine ⟨by nlinarith [mul_nonneg ha (sub_nonneg.mpr hu.1),
        mul_nonneg hb (sub_nonneg.mpr hv.1)], ?_⟩
      intro he
      by_cases hz : a = 0
      · have hb' : b = 1 := by linarith
        have hv' : l v = m := by simpa [hz, hb'] using he
        simpa [hz, hb'] using hv.2 hv'
      by_cases hz' : b = 0
      · have ha' : a = 1 := by linarith
        have hu' : l u = m := by simpa [hz', ha'] using he
        simpa [hz', ha'] using hu.2 hu'
      have hlu : l u = m := by
        by_contra hn
        have hh := mul_pos (lt_of_le_of_ne ha (Ne.symm hz)) (sub_pos.mpr (lt_of_le_of_ne hu.1 hn))
        nlinarith [mul_nonneg hb (sub_nonneg.mpr hv.1)]
      have hlv : l v = m := by
        by_contra hn
        have hh := mul_pos (lt_of_le_of_ne hb (Ne.symm hz')) (sub_pos.mpr (lt_of_le_of_ne hv.1 hn))
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hu.1)]
      exact (convex_convexHull ℝ _) (hu.2 hlu) (hv.2 hlv) ha hb hab
  apply Set.Subset.antisymm
  · intro x hx
    exact (hT hx.1).2 hx.2
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ _ hx.1, hx.2⟩
    · intro u hu v hv a b ha hb hab
      change _ ∧ l (a • u + b • v) = m
      refine ⟨(convex_convexHull ℝ S) hu.1 hv.1 ha hb hab, ?_⟩
      simp only [map_add, map_smul, smul_eq_mul, hu.2, hv.2, ← add_mul, hab, one_mul]

end
end G366022
```

## Edges.lean

```lean
import Geometry

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

def Edge (r s : R) : Prop :=
  r ≠ s ∧ ∃ (l : R →ₗ[ℝ] ℝ) (m : ℝ), (∀ x ∈ P, l x ≤ m) ∧
    face P l m = segment ℝ r s

theorem Edge.symm {r s : R} (e : Edge r s) : Edge s r := by
  obtain ⟨hn,l,m,hu,hf⟩ := e
  exact ⟨hn.symm,l,m,hu,hf.trans (segment_symm ℝ r s)⟩

private theorem face_of_generators (l : R →ₗ[ℝ] ℝ) (m : ℝ) (S : Set R)
    (hmax : ∀ i, l (g i) ≤ m)
    (hactive : ∀ i, l (g i) = m ↔ g i ∈ S)
    (hS : S ⊆ Set.range g) :
    (∀ x ∈ P, l x ≤ m) ∧ face P l m = convexHull ℝ S := by
  have hbound : P ⊆ {x | l x ≤ m} := by
    apply convexHull_min
    · rintro _ ⟨i,rfl⟩
      exact hmax i
    · intro u hu v hv a b ha hb hab
      change l u ≤ m at hu
      change l v ≤ m at hv
      change l (a • u + b • v) ≤ m
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        a * l u + b * l v ≤ a * m + b * m :=
          add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
        _ = m := by rw [← add_mul, hab, one_mul]
  refine ⟨fun _ hx => hbound hx, ?_⟩
  rw [P, face_hull _ _ _ (by rintro _ ⟨i,rfl⟩; exact hmax i)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩
    exact (hactive i).mp hi
  · intro hs
    obtain ⟨i,rfl⟩ := hS hs
    exact ⟨⟨i,rfl⟩,(hactive i).mpr hs⟩

private theorem face_of_indices (l : R →ₗ[ℝ] ℝ) (I : Set (Fin 8))
    (hmax : ∀ i, l (g i) ≤ 0) (hactive : ∀ i, l (g i) = 0 ↔ i ∈ I) :
    (∀ x ∈ P, l x ≤ 0) ∧ face P l 0 = convexHull ℝ (g '' I) := by
  apply face_of_generators l 0 (g '' I) hmax
  · intro i
    constructor
    · intro hi
      exact ⟨i,(hactive i).mp hi,rfl⟩
    · rintro ⟨j,hj,he⟩
      rw [← he]
      exact (hactive j).mpr hj
  · exact Set.image_subset_range _ _

theorem triangle013_face :
    (∀ x ∈ P, coeff ![0,0,-1,0] x ≤ 0) ∧
      face P (coeff ![0,0,-1,0]) 0 = convexHull ℝ (g '' ({0,2,4} : Set (Fin 8))) := by
  apply face_of_indices <;> intro i <;> fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

theorem triangle134_face :
    (∀ x ∈ P, coeff ![-1,0,0,0] x ≤ 0) ∧
      face P (coeff ![-1,0,0,0]) 0 = convexHull ℝ (g '' ({1,3,5} : Set (Fin 8))) := by
  apply face_of_indices <;> intro i <;> fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

private theorem edge_of_indices (i j : Fin 8) (hn : g i ≠ g j)
    (l : R →ₗ[ℝ] ℝ) (hmax : ∀ k, l (g k) ≤ 0)
    (hactive : ∀ k, l (g k) = 0 ↔ k ∈ ({i,j} : Set (Fin 8))) : Edge (g i) (g j) := by
  obtain ⟨hu,hf⟩ := face_of_indices l {i,j} hmax hactive
  refine ⟨hn,l,0,hu,?_⟩
  rw [hf, Set.image_insert_eq, Set.image_singleton, convexHull_pair]

theorem edge12 : Edge (g 0) (g 2) := by
  apply edge_of_indices 0 2 (l := coeff ![0,0,-3,-1])
  · intro hEq
    have hc := congrFun hEq 0
    norm_num [g,gQ] at hc
  all_goals intro i; fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

theorem edge14 : Edge (g 0) (g 4) := by
  apply edge_of_indices 0 4 (l := coeff ![0,-1,-3,0])
  · intro hEq
    have hc := congrFun hEq 0
    norm_num [g,gQ] at hc
  all_goals intro i; fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

theorem edge23 : Edge (g 1) (g 3) := by
  apply edge_of_indices 1 3 (l := coeff ![-5,0,0,-1])
  · intro hEq
    have hc := congrFun hEq 2
    norm_num [g,gQ] at hc
  all_goals intro i; fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

theorem edge34 : Edge (g 1) (g 5) := by
  apply edge_of_indices 1 5 (l := coeff ![-3,-1,0,0])
  · intro hEq
    have hc := congrFun hEq 2
    norm_num [g,gQ] at hc
  all_goals intro i; fin_cases i <;>
    norm_num [coeff_apply, g, gQ, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceFinMk]

private theorem endpoint_generator {r s : R} (e : Edge r s) : r ∈ Set.range g := by
  obtain ⟨hn,l,m,hu,hf⟩ := e
  have he : ∃ k, r k ≠ s k := by
    by_contra! he
    exact hn (funext he)
  obtain ⟨k,hk⟩ := he
  let a : R →ₗ[ℝ] ℝ :=
    (r k - s k) • LinearMap.proj k
  have ha (x : R) : a x = (r k - s k) * x k := rfl
  have hs : a s < a r := by
    simp only [ha]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hk)]
  let S : Set R := {x ∈ Set.range g | l x = m}
  have hS : convexHull ℝ S = segment ℝ r s := (face_hull _ _ _ (fun x hx =>
    hu x (subset_convexHull ℝ _ hx))).symm.trans hf
  have side {x : R} (hx : x ∈ segment ℝ r s) : a x ≤ a r ∧ (a x = a r → x = r) := by
    obtain ⟨u,v,_,hv,hsum,rfl⟩ := hx
    simp only [map_add, map_smul, smul_eq_mul]
    have hp := mul_nonneg hv (sub_nonneg.mpr hs.le)
    refine ⟨by nlinarith [congrArg (fun b => b * a r) hsum], ?_⟩
    intro he
    have hz : v = 0 := by
      by_contra hne
      have ht := mul_pos (lt_of_le_of_ne hv (Ne.symm hne)) (sub_pos.mpr hs)
      nlinarith [congrArg (fun b => b * a r) hsum]
    have ho : u = 1 := by linarith
    simp [hz, ho]
  have hbound (x : R) (hx : x ∈ S) : a x ≤ a r :=
    (side (hS ▸ subset_convexHull ℝ S hx)).1
  have hmem : r ∈ convexHull ℝ {x ∈ S | a x = a r} := by
    rw [← face_hull S a (a r) hbound, hS]
    exact ⟨left_mem_segment ℝ r s,rfl⟩
  by_contra hnot
  have he : {x ∈ S | a x = a r} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := (side (hS ▸ subset_convexHull ℝ S hx.1)).2 hx.2
    exact hnot (hx' ▸ hx.1.1)
  simp [he] at hmem

theorem edge_generators {r s : R} (e : Edge r s) :
    r ∈ Set.range g ∧ s ∈ Set.range g :=
  ⟨endpoint_generator e, endpoint_generator e.symm⟩

theorem coeff_representation (l : R →ₗ[ℝ] ℝ) :
    l = coeff ![l ![1,0,0,0], l ![0,1,0,0], l ![0,0,1,0], l ![0,0,0,1]] := by
  apply LinearMap.ext
  intro x
  have hx : x = x 0 • ![1,0,0,0] + x 1 • ![0,1,0,0] +
      x 2 • ![0,0,1,0] + x 3 • ![0,0,0,1] := by
    ext i
    fin_cases i <;> simp [Fin.reduceFinMk]
  calc
    l x = l (x 0 • ![1,0,0,0] + x 1 • ![0,1,0,0] +
      x 2 • ![0,0,1,0] + x 3 • ![0,0,0,1]) := congrArg l hx
    _ = _ := by
      simp only [map_add, map_smul, smul_eq_mul, coeff_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
      change x 0 * l ![1,0,0,0] + x 1 * l ![0,1,0,0] + x 2 * l ![0,0,1,0] + x 3 * l ![0,0,0,1] =
        l ![1,0,0,0] * x 0 + l ![0,1,0,0] * x 1 + l ![0,0,1,0] * x 2 + l ![0,0,0,1] * x 3
      ring

private theorem forbid_planar (i j : Fin 8) (hi : i.val < 4) (hj : j.val < 4)
    (e : Edge (g i) (g j)) :
    (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) ∨ (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) := by
  obtain ⟨hne,l,m,hu,hf⟩ := e
  have hri : l (g i) = m := by
    have hmem : g i ∈ face P l m := hf.symm ▸ left_mem_segment ℝ (g i) (g j)
    exact hmem.2
  have hrj : l (g j) = m := by
    have hmem : g j ∈ face P l m := hf.symm ▸ right_mem_segment ℝ (g i) (g j)
    exact hmem.2
  have h0 := hu _ (g_mem 0)
  have h1 := hu _ (g_mem 1)
  have h2 := hu _ (g_mem 2)
  have h3 := hu _ (g_mem 3)
  have h4 := hu _ (g_mem 4)
  have h5 := hu _ (g_mem 5)
  have h6 := hu _ (g_mem 6)
  have h7 := hu _ (g_mem 7)
  have hlimit : l (g 4) ≠ m := by
    intro he
    have hh : g 4 ∈ segment ℝ (g i) (g j) := hf ▸ (show g 4 ∈ face P l m from ⟨g_mem 4,he⟩)
    obtain ⟨a,b,_,_,_,heq⟩ := hh
    have hi' : g i 3 = 0 := by
      fin_cases i <;> (first | (norm_num [g,gQ,Fin.reduceFinMk]; done) | (exfalso; exact (by decide : ¬ (_ < 4)) hi))
    have hj' : g j 3 = 0 := by
      fin_cases j <;> (first | (norm_num [g,gQ,Fin.reduceFinMk]; done) | (exfalso; exact (by decide : ¬ (_ < 4)) hj))
    have hcoord := congrFun heq 3
    simp only [Pi.add_apply, Pi.smul_apply, hi', hj', smul_eq_mul, mul_zero, add_zero] at hcoord
    norm_num [g,gQ] at hcoord
  have hd : i ≠ j := fun h => hne (congrArg g h)
  obtain ⟨w,hw⟩ : ∃ w : R, l = coeff w := ⟨_,coeff_representation l⟩
  rw [hw] at hri hrj h0 h1 h2 h3 h4 h5 h6 h7 hlimit
  norm_num [coeff_apply,g,gQ] at h0 h1 h2 h3 h4 h5 h6 h7 hlimit
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Fin.reduceFinMk] at hi
  all_goals try norm_num [Fin.reduceFinMk] at hj
  all_goals try norm_num [Fin.reduceFinMk] at hd
  all_goals norm_num [Fin.reduceFinMk]
  all_goals
    exfalso
    apply hlimit
    norm_num [coeff_apply,g,gQ,Fin.reduceFinMk] at hri hrj
    linarith

theorem planar_edges_iff (i j : Fin 8) (hi : i.val < 4) (hj : j.val < 4) :
    Edge (g i) (g j) ↔
      (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) ∨ (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) := by
  constructor
  · exact forbid_planar i j hi hj
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact edge12
    · exact edge12.symm
    · exact edge23
    · exact edge23.symm

theorem planar_generator_iff (i : Fin 8) : g i 3 = 0 ↔ i.val < 4 := by
  fin_cases i <;> norm_num [g,gQ,Fin.reduceFinMk]

end
end G366022
```

## Interior.lean

```lean
import Geometry
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

def Graph (a b c d : ℝ) : Submodule ℝ R where
  carrier := {x | x 2 = a*x 0 + c*x 1 ∧ x 3 = b*x 0 + d*x 1}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    change ((x+y) 2 = _) ∧ ((x+y) 3 = _)
    simp only [Pi.add_apply, hx, hx', hy, hy']
    constructor <;> ring
  smul_mem' := by
    rintro k x ⟨hx,hx'⟩
    change ((k • x) 2 = _) ∧ ((k • x) 3 = _)
    simp only [Pi.smul_apply, smul_eq_mul, hx, hx']
    constructor <;> ring

theorem mem_graph {a b c d : ℝ} {x : R} :
    x ∈ Graph a b c d ↔ x 2 = a*x 0+c*x 1 ∧ x 3 = b*x 0+d*x 1 := Iff.rfl

def graphEquiv (a b c d : ℝ) : (Fin 2 → ℝ) ≃ₗ[ℝ] Graph a b c d where
  toFun x := ⟨![x 0,x 1,a*x 0+c*x 1,b*x 0+d*x 1], by
    rw [mem_graph]
    constructor <;> rfl⟩
  invFun x := ![x.val 0,x.val 1]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    obtain ⟨hx,hy⟩ := mem_graph.mp x.property
    fin_cases i
    · rfl
    · rfl
    · exact hx.symm
    · exact hy.symm
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · change a*(x 0+y 0)+c*(x 1+y 1) = (a*x 0+c*x 1)+(a*y 0+c*y 1)
      ring
    · change b*(x 0+y 0)+d*(x 1+y 1) = (b*x 0+d*x 1)+(b*y 0+d*y 1)
      ring
  map_smul' k x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · change a*(k*x 0)+c*(k*x 1) = k*(a*x 0+c*x 1)
      ring
    · change b*(k*x 0)+d*(k*x 1) = k*(b*x 0+d*x 1)
      ring

theorem graph_finrank (a b c d : ℝ) : Module.finrank ℝ (Graph a b c d) = 2 := by
  rw [← (graphEquiv a b c d).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

def t : ℝ := 1/1000
def signedT (plus : Bool) : ℝ := if plus then t else -t
def row0 (a b : ℝ) : R := ![1,0,a,b]
def row1 (c d : ℝ) : R := ![0,1,c,d]

def z (plus : Bool) : R := row0 1 (signedT plus) + row1 (signedT plus) (t^2/2)

theorem z_h_pos (plus : Bool) : 0 < h (z plus) := by
  cases plus <;> norm_num [h_apply,z,row0,row1,signedT,t]

def witness (plus : Bool) : H :=
  ⟨(h (z plus))⁻¹ • z plus, by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt (z_h_pos plus))]⟩

theorem witness_graph (plus : Bool) :
    (witness plus).val ∈ Graph 1 (signedT plus) (signedT plus) (t^2/2) := by
  apply Submodule.smul_mem
  rw [mem_graph]
  simp [z,row0,row1,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,add_comm]

private def k : ℝ := 1/100
private def wU (x : R) : ℝ := x 1 + k
private def wV (x : R) : ℝ := x 3 + k
private def w0 (x : R) : ℝ := x 0 - (wU x + wV x)/2 - 3*k/2
private def w1 (x : R) : ℝ := x 2 - (wU x + wV x)/2 - 3*k/2
private def weights (x : R) : Fin 8 → ℝ :=
  ![w0 x,w1 x,wU x,wU x,wV x,wV x,k,0]

def region : Set H :=
  {x | 0 < w0 x.val ∧ 0 < w1 x.val ∧ 0 < wU x.val ∧ 0 < wV x.val}

theorem region_open : IsOpen region := by
  have hx (i : Fin 4) : Continuous (fun x : H => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have h2 : Continuous (fun x : H => wU x.val) := (hx 1).add continuous_const
  have h3 : Continuous (fun x : H => wV x.val) := (hx 3).add continuous_const
  have hmid : Continuous (fun x : H => (wU x.val + wV x.val)/2) :=
    (h2.add h3).div_const _
  have h0 : Continuous (fun x : H => w0 x.val) := ((hx 0).sub hmid).sub continuous_const
  have h1 : Continuous (fun x : H => w1 x.val) := ((hx 2).sub hmid).sub continuous_const
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt continuous_const h1).inter
    ((isOpen_lt continuous_const h2).inter (isOpen_lt continuous_const h3)))

theorem region_subset : region ⊆ PChart := by
  rintro x ⟨h0,h1,h2,h3⟩
  change x.val ∈ P
  have hs : ∑ i : Fin 8, weights x.val i = 1 := by
    have hsum := x.property
    rw [h_apply] at hsum
    simp [Fin.sum_univ_succ, weights, w0,w1,wU,wV,Fin.reduceFinMk]
    linarith
  have hcomb : (∑ i : Fin 8, weights x.val i • g i) = x.val := by
    ext j
    fin_cases j <;>
      norm_num [Fin.sum_univ_succ, weights,w0,w1,wU,wV,g,gQ,Fin.reduceFinMk,
        Finset.sum_apply,Pi.add_apply,Pi.smul_apply] <;> ring
  rw [← hcomb]
  refine (convex_convexHull ℝ (Set.range g)).sum_mem (t := Finset.univ)
    (w := weights x.val) ?_ hs (fun i _ => g_mem i)
  intro i _
  fin_cases i <;>
    first | exact h0.le | exact h1.le | exact h2.le | exact h3.le |
      norm_num [weights,k,Fin.reduceFinMk]

theorem witness_region (plus : Bool) : witness plus ∈ region := by
  cases plus <;>
    norm_num [region,witness,weights,w0,w1,wU,wV,k,z,row0,row1,h_apply,signedT,t,
      Pi.smul_apply,Pi.add_apply]

theorem witness_interior (plus : Bool) : witness plus ∈ interior PChart :=
  interior_maximal region_subset region_open (witness_region plus)

theorem chart_interior_nonempty : (interior PChart).Nonempty :=
  ⟨witness true, witness_interior true⟩

end
end G366022
```

## Chow.lean

```lean
import Edges
import Interior

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

def stack (u v r s : R) : Matrix (Fin 4) (Fin 4) ℝ := ![u,v,r,s]

theorem stack_det (u v r s : R) :
    (stack u v r s).det =
      (-1 : ℝ)^0 * u 0 * (v 1 * r 2 * s 3 - v 1 * r 3 * s 2 -
        v 2 * r 1 * s 3 + v 2 * r 3 * s 1 + v 3 * r 1 * s 2 - v 3 * r 2 * s 1) +
      (-1 : ℝ)^1 * u 1 * (v 0 * r 2 * s 3 - v 0 * r 3 * s 2 -
        v 2 * r 0 * s 3 + v 2 * r 3 * s 0 + v 3 * r 0 * s 2 - v 3 * r 2 * s 0) +
      (-1 : ℝ)^2 * u 2 * (v 0 * r 1 * s 3 - v 0 * r 3 * s 1 -
        v 1 * r 0 * s 3 + v 1 * r 3 * s 0 + v 3 * r 0 * s 1 - v 3 * r 1 * s 0) +
      (-1 : ℝ)^3 * u 3 * (v 0 * r 1 * s 2 - v 0 * r 2 * s 1 -
        v 1 * r 0 * s 2 + v 1 * r 2 * s 0 + v 2 * r 0 * s 1 - v 2 * r 1 * s 0) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three]
  rfl

def chow (a b c d : ℝ) (r s : R) : ℝ :=
  (stack (row0 a b) (row1 c d) r s).det

def qx {K : Type*} [Ring K] (a c : K) (x : Fin 4 → K) : K :=
  x 2 - a*x 0 - c*x 1

def qy {K : Type*} [Ring K] (b d : K) (x : Fin 4 → K) : K :=
  x 3 - b*x 0 - d*x 1

def quotientDet {K : Type*} [Ring K] (a b c d : K) (r s : Fin 4 → K) : K :=
  qx a c r * qy b d s - qy b d r * qx a c s

theorem chow_quotient (a b c d : ℝ) (r s : R) :
    chow a b c d r s = quotientDet a b c d r s := by
  rw [chow, stack_det]
  simp [row0,row1,quotientDet,qx,qy,Matrix.vecHead,Matrix.vecTail]
  ring

theorem chow_swap (a b c d : ℝ) (r s : R) :
    chow a b c d s r = -chow a b c d r s := by
  rw [chow_quotient, chow_quotient]
  unfold quotientDet
  ring

theorem chow12 (a b c d : ℝ) : chow a b c d (g 0) (g 2) = (a*d-b*c)/2 := by
  rw [chow_quotient]
  norm_num [quotientDet,qx,qy,g,gQ]
  ring

theorem chow14 (a b c d : ℝ) : chow a b c d (g 0) (g 4) = -a/2 := by
  rw [chow_quotient]
  norm_num [quotientDet,qx,qy,g,gQ]
  ring

theorem chow23 (a b c d : ℝ) : chow a b c d (g 1) (g 3) = -d/2 := by
  rw [chow_quotient]
  norm_num [quotientDet,qx,qy,g,gQ]
  ring

theorem chow34 (a b c d : ℝ) : chow a b c d (g 1) (g 5) = 1/2 := by
  rw [chow_quotient]
  norm_num [quotientDet,qx,qy,g,gQ]

def witnessChow (plus : Bool) : R → R → ℝ :=
  chow 1 (signedT plus) (signedT plus) (t^2/2)

theorem witnessChow12 (plus : Bool) : witnessChow plus (g 0) (g 2) = -t^2/4 := by
  unfold witnessChow
  rw [chow12]
  cases plus <;> simp [signedT] <;> ring

theorem witnessChow14 (plus : Bool) : witnessChow plus (g 0) (g 4) = -1/2 := by
  unfold witnessChow
  rw [chow14]

theorem witnessChow23 (plus : Bool) : witnessChow plus (g 1) (g 3) = -t^2/4 := by
  unfold witnessChow
  rw [chow23]
  ring

theorem witnessChow34 (plus : Bool) : witnessChow plus (g 1) (g 5) = 1/2 :=
  chow34 _ _ _ _

private def tQ : ℚ := 1/1000

private theorem rat_nonplanar :
    ∀ i j : Fin 8, i ≠ j → (4 ≤ i.val ∨ 4 ≤ j.val) →
      0 < quotientDet 1 tQ tQ (tQ^2/2) (gQ i) (gQ j) *
        quotientDet 1 (-tQ) (-tQ) (tQ^2/2) (gQ i) (gQ j) := by
  intro i j hij hn
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Fin.reduceFinMk] at hij
  all_goals try norm_num [Fin.reduceFinMk] at hn
  all_goals norm_num [quotientDet,qx,qy,tQ,gQ,Fin.reduceFinMk]

private theorem cast_qdet (a b c d : ℚ) (i j : Fin 8) :
    ((quotientDet a b c d (gQ i) (gQ j) : ℚ) : ℝ) =
      quotientDet (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (g i) (g j) := by
  simp [quotientDet,qx,qy,g]

private theorem nonplanar_sign {i j : Fin 8} (hne : i ≠ j) (hij : 4 ≤ i.val ∨ 4 ≤ j.val) :
    0 < witnessChow true (g i) (g j) * witnessChow false (g i) (g j) := by
  have hrat := rat_nonplanar i j hne hij
  have hh : (0 : ℝ) < ((quotientDet 1 tQ tQ (tQ^2/2) (gQ i) (gQ j) *
        quotientDet 1 (-tQ) (-tQ) (tQ^2/2) (gQ i) (gQ j) : ℚ) : ℝ) := by exact_mod_cast hrat
  have ht : (tQ : ℝ) = t := by norm_num [tQ,t]
  push_cast [cast_qdet, ht] at hh
  change 0 < chow 1 t t (t^2/2) (g i) (g j) *
    chow 1 (-t) (-t) (t^2/2) (g i) (g j)
  simpa only [chow_quotient] using hh

theorem all_edge_product_pos {r s : R} (he : Edge r s) :
    0 < witnessChow true r s * witnessChow false r s := by
  obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := edge_generators he
  by_cases hi : i.val < 4
  · by_cases hj : j.val < 4
    · rcases (planar_edges_iff i j hi hj).mp he with
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · norm_num [witnessChow12,t]
      · have hswap (p : Bool) : witnessChow p (g 2) (g 0) =
            -witnessChow p (g 0) (g 2) := chow_swap _ _ _ _ _ _
        norm_num [hswap,witnessChow12,t]
      · norm_num [witnessChow23,t]
      · have hswap (p : Bool) : witnessChow p (g 3) (g 1) =
            -witnessChow p (g 1) (g 3) := chow_swap _ _ _ _ _ _
        norm_num [hswap,witnessChow23,t]
    · exact nonplanar_sign (fun hh => he.1 (congrArg g hh)) (Or.inr (le_of_not_gt hj))
  · exact nonplanar_sign (fun hh => he.1 (congrArg g hh)) (Or.inl (le_of_not_gt hi))

theorem all_edge_strict_signs {r s : R} (he : Edge r s) :
    (0 < witnessChow true r s ∧ 0 < witnessChow false r s) ∨
      (witnessChow true r s < 0 ∧ witnessChow false r s < 0) :=
  mul_pos_iff.mp (all_edge_product_pos he)

end
end G366022
```

## NativeEdges.lean

```lean
import Edges
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace G366022
noncomputable section

def ExposedEdgeFace (F : Set R) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ F : Submodule ℝ R) = 1 ∧
    ∃ (l : R →ₗ[ℝ] ℝ) (m : ℝ), (∀ x ∈ P, l x ≤ m) ∧ F = face P l m

private theorem nontrivial_of_dim_one {F : Set R}
    (hd : Module.finrank ℝ (vectorSpan ℝ F : Submodule ℝ R) = 1) : F.Nontrivial := by
  by_contra h
  have hs := Set.not_nontrivial_iff.mp h
  rcases F.eq_empty_or_nonempty with hempty | ⟨r,hr⟩
  · rw [hempty, vectorSpan_empty, finrank_bot] at hd
    omega
  · have hsub : F ⊆ {r} := fun _ hx => Set.mem_singleton_iff.mpr (hs hx hr)
    have hb : (vectorSpan ℝ F : Submodule ℝ R) = ⊥ := by
      apply bot_unique
      simpa only [vectorSpan_singleton] using vectorSpan_mono ℝ hsub
    rw [hb, finrank_bot] at hd
    omega

private theorem compact_collinear_segment {F : Set R} (hc : IsCompact F)
    (hv : Convex ℝ F) (hcol : Collinear ℝ F) (hnt : F.Nontrivial) :
    ∃ r s, r ≠ s ∧ F = segment ℝ r s := by
  obtain ⟨p,hp,q,hq,hpq⟩ := hnt
  obtain ⟨v,hvline⟩ := (collinear_iff_of_mem hp).mp hcol
  have hv0 : v ≠ 0 := by
    intro he
    obtain ⟨c,hc⟩ := hvline q hq
    apply hpq
    symm
    change q = c • v + p at hc
    simpa [he] using hc
  obtain ⟨i,hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
    by_contra! hh
    exact hv0 (funext hh)
  have hinj : Set.InjOn (fun x : R => x i) F := by
    intro x hx y hy hxy
    obtain ⟨a,ha⟩ := hvline x hx
    obtain ⟨b,hb⟩ := hvline y hy
    change x = a • v + p at ha
    change y = b • v + p at hb
    rw [ha,hb] at hxy
    change a * v i + p i = b * v i + p i at hxy
    have hab := mul_right_cancel₀ hi (add_right_cancel hxy)
    rw [ha,hb,hab]
  obtain ⟨r,hr,hmin⟩ := hc.exists_isMinOn ⟨p,hp⟩ (continuous_apply i).continuousOn
  obtain ⟨s,hs,hmax⟩ := hc.exists_isMaxOn ⟨p,hp⟩ (continuous_apply i).continuousOn
  have hlt : r i < s i := by
    refine lt_of_le_of_ne (hmin hs) ?_
    intro he
    apply hpq
    apply hinj hp hq
    have hpmin := hmin hp
    have hpmax := hmax hp
    have hqmin := hmin hq
    have hqmax := hmax hq
    change r i ≤ p i at hpmin
    change p i ≤ s i at hpmax
    change r i ≤ q i at hqmin
    change q i ≤ s i at hqmax
    linarith
  refine ⟨r,s,fun he => hlt.ne (congrFun he i), Set.Subset.antisymm ?_ (hv.segment_subset hr hs)⟩
  intro x hx
  let b := (x i - r i) / (s i - r i)
  have hden : 0 < s i - r i := sub_pos.mpr hlt
  have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr (hmin hx)) hden.le
  have hb1 : b ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right (hmax hx) _)
  have ha : 0 ≤ 1 - b := sub_nonneg.mpr hb1
  have hab : 1 - b + b = 1 := by ring
  refine ⟨1-b,b,ha,hb0,hab,?_⟩
  apply hinj (hv hr hs ha hb0 hab) hx
  change (1-b)*r i + b*s i = x i
  have hid : b * (s i - r i) = x i - r i := div_mul_cancel₀ _ hden.ne'
  linarith

theorem edge_iff_dim_one {r s : R} :
    Edge r s ↔ r ≠ s ∧ ExposedEdgeFace (segment ℝ r s) := by
  constructor
  · rintro ⟨hne,l,m,hu,hf⟩
    refine ⟨hne,?_,l,m,hu,hf.symm⟩
    rw [← convexHull_pair, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (sub_ne_zero.mpr hne)
  · rintro ⟨hne,_,l,m,hu,hf⟩
    exact ⟨hne,l,m,hu,hf.symm⟩

theorem dim_one_face_iff (F : Set R) :
    ExposedEdgeFace F ↔ ∃ r s, Edge r s ∧ F = segment ℝ r s := by
  constructor
  · rintro ⟨hd,l,m,hu,hf⟩
    have hHull : F = convexHull ℝ {x ∈ Set.range g | l x = m} :=
      hf.trans (face_hull _ _ _ (fun x hx => hu x (subset_convexHull ℝ _ hx)))
    have hfin : {x ∈ Set.range g | l x = m}.Finite :=
      (Set.finite_range g).subset fun _ hx => hx.1
    have hcmp : IsCompact F := hHull ▸ hfin.isCompact_convexHull (𝕜 := ℝ)
    have hcv : Convex ℝ F := hHull ▸ convex_convexHull ℝ _
    have hcol : Collinear ℝ F := (collinear_iff_finrank_le_one (k := ℝ)).mpr (by rw [hd])
    obtain ⟨r,s,hne,hseg⟩ := compact_collinear_segment hcmp hcv hcol (nontrivial_of_dim_one hd)
    exact ⟨r,s,⟨hne,l,m,hu,hf.symm.trans hseg⟩,hseg⟩
  · rintro ⟨r,s,he,rfl⟩
    exact (edge_iff_dim_one.mp he).2

end
end G366022
```

## Interface.lean

```lean
import Chow
import NativeEdges

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

def spanPair (r s : R) : Submodule ℝ R := Submodule.span ℝ {r,s}

def e (i : Fin 4) : R := Pi.single i 1

def axis (i j : Fin 4) : Submodule ℝ R := spanPair (e i) (e j)

theorem mem_spanPair {r s x : R} :
    x ∈ spanPair r s ↔ ∃ a b : ℝ, a • r + b • s = x := by
  exact Submodule.mem_span_pair

theorem left_spanPair (r s : R) : r ∈ spanPair r s :=
  Submodule.subset_span (by simp)

theorem right_spanPair (r s : R) : s ∈ spanPair r s :=
  Submodule.subset_span (by simp)

theorem span_segment (r s : R) :
    Submodule.span ℝ (segment ℝ r s) = spanPair r s := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a,b,_,_,_,rfl⟩
    exact mem_spanPair.mpr ⟨a,b,rfl⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with he | hx
    · rw [he]
      exact Submodule.subset_span (left_mem_segment ℝ r s)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Submodule.subset_span (right_mem_segment ℝ r s)

private theorem half_span (r s : R) :
    spanPair r ((1/2 : ℝ) • (r+s)) = spanPair r s := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with he | hx
    · rw [he]
      exact left_spanPair r s
    · rw [Set.mem_singleton_iff.mp hx]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (left_spanPair r s) (right_spanPair r s))
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with he | hx
    · rw [he]
      exact left_spanPair _ _
    · rw [Set.mem_singleton_iff.mp hx]
      have hmem := Submodule.sub_mem _ (Submodule.smul_mem _ (2 : ℝ)
        (right_spanPair r ((1/2 : ℝ) • (r+s)))) (left_spanPair r ((1/2 : ℝ) • (r+s)))
      simpa [smul_smul] using hmem

theorem span12 : spanPair (g 0) (g 2) = axis 0 1 := by
  have h0 : g 0 = e 0 := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  have h2 : g 2 = (1/2 : ℝ) • (e 0 + e 1) := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  rw [h0,h2,half_span,axis]

theorem span14 : spanPair (g 0) (g 4) = axis 0 3 := by
  have h0 : g 0 = e 0 := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  have h4 : g 4 = (1/2 : ℝ) • (e 0 + e 3) := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  rw [h0,h4,half_span,axis]

theorem span23 : spanPair (g 1) (g 3) = axis 1 2 := by
  have h1 : g 1 = e 2 := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  have h3 : g 3 = (1/2 : ℝ) • (e 2 + e 1) := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  rw [h1,h3,half_span,axis,spanPair,spanPair,Set.pair_comm]

theorem span34 : spanPair (g 1) (g 5) = axis 2 3 := by
  have h1 : g 1 = e 2 := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  have h5 : g 5 = (1/2 : ℝ) • (e 2 + e 3) := by
    ext i; fin_cases i <;> norm_num [g,gQ,e,Pi.single_apply,Fin.reduceFinMk]
  rw [h1,h5,half_span,axis]

def p12 (u v : R) : ℝ := u 0 * v 1 - u 1 * v 0

theorem stack34 (u v : R) : (stack u v (g 1) (g 5)).det = p12 u v / 2 := by
  rw [stack_det]
  norm_num [g,gQ,p12]
  ring

def Away (W : Submodule ℝ R) : Prop :=
  ∀ r s, Edge r s → Disjoint W (spanPair r s)

def Stabs (W : Submodule ℝ R) : Prop :=
  ∃ x : H, x ∈ PChart ∧ x.val ∈ W

def StabComplement (W : Submodule ℝ R) : Prop :=
  Module.finrank ℝ W = 2 ∧ Stabs W ∧ Away W

def signPattern (a b c d : ℝ) : Prop :=
  ∀ r s, Edge r s → 0 < chow a b c d r s * witnessChow true r s

theorem chart_separation (a b c d : ℝ) (hh : signPattern a b c d) :
    0 < a*d ∧ a*d < b*c := by
  have h12 := hh _ _ edge12
  have h14 := hh _ _ edge14
  have h23 := hh _ _ edge23
  rw [chow12,witnessChow12] at h12
  rw [chow14,witnessChow14] at h14
  rw [chow23,witnessChow23] at h23
  norm_num [t] at h12 h14 h23
  exact ⟨mul_pos (by linarith) (by linarith), by linarith⟩

theorem chart_b_ne_zero (a b c d : ℝ) (hh : signPattern a b c d) : b ≠ 0 := by
  intro hzero
  obtain ⟨hp,hlt⟩ := chart_separation a b c d hh
  rw [hzero,zero_mul] at hlt
  exact (not_lt_of_ge hp.le) hlt

theorem certificate :
    (∃ x : H, x ∈ interior PChart ∧ x.val ∈ Graph 1 t t (t^2/2)) ∧
    (∃ x : H, x ∈ interior PChart ∧ x.val ∈ Graph 1 (-t) (-t) (t^2/2)) ∧
    ∀ r s, Edge r s → 0 < witnessChow true r s * witnessChow false r s := by
  exact ⟨⟨witness true,witness_interior true,witness_graph true⟩,
    ⟨witness false,witness_interior false,witness_graph false⟩,
    fun _ _ he => all_edge_product_pos he⟩

end
end G366022
```

## Incidence.lean

```lean
import Interface
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

theorem edge_endpoint_chart {r s : R} (he : Edge r s) : h r = 1 ∧ h s = 1 := by
  obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := edge_generators he
  exact ⟨h_g i,h_g j⟩

theorem edge_basis {r s : R} (he : Edge r s) :
    LinearIndependent ℝ (![r,s] : Fin 2 → R) := by
  obtain ⟨hr,hs⟩ := edge_endpoint_chart he
  rw [linearIndependent_fin2]
  change s ≠ 0 ∧ ∀ a : ℝ, a • s ≠ r
  constructor
  · intro hzero
    simp [hzero] at hs
  · intro a ha
    have hscalar := congrArg h ha
    have ha1 : a = 1 := by
      simpa only [map_smul, smul_eq_mul, hs, hr, mul_one] using hscalar
    apply he.1
    simpa [ha1] using ha.symm

theorem graph_span (a b c d : ℝ) : Graph a b c d = spanPair (row0 a b) (row1 c d) := by
  ext x
  rw [mem_graph,mem_spanPair]
  constructor
  · intro hx
    refine ⟨x 0,x 1,?_⟩
    ext i
    fin_cases i <;> simp [row0,row1,Fin.reduceFinMk,hx.1,hx.2,mul_comm]
  · rintro ⟨p,q,rfl⟩
    simp [row0,row1,mul_comm]

theorem graph_basis (a b c d : ℝ) :
    LinearIndependent ℝ (![row0 a b,row1 c d] : Fin 2 → R) := by
  rw [linearIndependent_fin2]
  change row1 c d ≠ 0 ∧ ∀ x : ℝ, x • row1 c d ≠ row0 a b
  constructor
  · intro hh
    have he := congrFun hh 1
    norm_num [row1] at he
  · intro x hh
    have he := congrFun hh 0
    norm_num [row1,row0] at he

private theorem pair_coeff_zero {u v : R}
    (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R))
    {a b : ℝ} (hz : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have hh := (Fintype.linearIndependent_iff.mp hl) (![a,b] : Fin 2 → ℝ)
    (by simpa [Fin.sum_univ_two] using hz)
  exact ⟨hh 0,hh 1⟩

private theorem stack_coeff_zero {u v r s : R}
    (hl : LinearIndependent ℝ (stack u v r s))
    {a b c d : ℝ} (hz : a • u + b • v + c • r + d • s = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hh := (Fintype.linearIndependent_iff.mp hl) (![a,b,c,d] : Fin 4 → ℝ)
    (by simpa [Fin.sum_univ_four,stack] using hz)
  exact ⟨hh 0,hh 1,hh 2,hh 3⟩

theorem det_ne_zero_iff_disjoint (u v r s : R)
    (huv : LinearIndependent ℝ (![u,v] : Fin 2 → R))
    (hrs : LinearIndependent ℝ (![r,s] : Fin 2 → R)) :
    (stack u v r s).det ≠ 0 ↔ Disjoint (spanPair u v) (spanPair r s) := by
  rw [Submodule.disjoint_def]
  constructor
  · intro hd x hx hy
    obtain ⟨a,b,hab⟩ := mem_spanPair.mp hx
    obtain ⟨c,d,hcd⟩ := mem_spanPair.mp hy
    have hz : a • u + b • v + (-c) • r + (-d) • s = 0 := by
      rw [neg_smul,neg_smul,hab,← hcd]
      abel
    obtain ⟨ha,hb,_,_⟩ := stack_coeff_zero (Matrix.linearIndependent_rows_of_det_ne_zero hd) hz
    simpa [ha,hb] using hab.symm
  · intro hd
    refine ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp ?_)).ne_zero
    change LinearIndependent ℝ (fun i : Fin 4 => stack u v r s i)
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hz : a 0 • u + a 1 • v + a 2 • r + a 3 • s = 0 := by
      simpa [Fin.sum_univ_four,stack] using ha
    let x := a 0 • u + a 1 • v
    have hab : (-a 2) • r + (-a 3) • s = x := by
      have hs : x + (a 2 • r + a 3 • s) = 0 := by
        dsimp [x]
        rwa [← add_assoc]
      calc
        (-a 2) • r + (-a 3) • s = x - (x + (a 2 • r + a 3 • s)) := by
          rw [neg_smul,neg_smul]
          abel
        _ = x := by rw [hs,sub_zero]
    have hzero : x = 0 := hd x (mem_spanPair.mpr ⟨_,_,rfl⟩) (mem_spanPair.mpr ⟨_,_,hab⟩)
    obtain ⟨h0,h1⟩ := pair_coeff_zero huv hzero
    obtain ⟨h2,h3⟩ := pair_coeff_zero hrs (hab.trans hzero)
    fin_cases i <;> simp [Fin.reduceFinMk,h0,h1,neg_eq_zero.mp h2,neg_eq_zero.mp h3]

theorem chow_ne_zero_iff (a b c d : ℝ) {r s : R} (he : Edge r s) :
    chow a b c d r s ≠ 0 ↔ Disjoint (Graph a b c d) (spanPair r s) := by
  rw [chow,graph_span]
  exact det_ne_zero_iff_disjoint _ _ _ _ (graph_basis _ _ _ _) (edge_basis he)

theorem p12_ne_zero_of_away {u v : R}
    (hb : LinearIndependent ℝ (![u,v] : Fin 2 → R))
    (ha : Away (spanPair u v)) : p12 u v ≠ 0 := by
  have hd := (det_ne_zero_iff_disjoint u v _ _ hb (edge_basis edge34)).mpr (ha _ _ edge34)
  rw [stack34] at hd
  exact fun hz => hd (by rw [hz,zero_div])

theorem graph_witness_stab_complement (plus : Bool) :
    StabComplement (Graph 1 (signedT plus) (signedT plus) (t^2/2)) := by
  refine ⟨graph_finrank _ _ _ _,⟨witness plus,interior_subset (witness_interior plus),
    witness_graph plus⟩,?_⟩
  intro r s he
  apply (chow_ne_zero_iff _ _ _ _ he).mp
  change witnessChow plus r s ≠ 0
  have hp := all_edge_strict_signs he
  cases plus
  · exact hp.elim (fun h => h.2.ne') (fun h => h.2.ne)
  · exact hp.elim (fun h => h.1.ne') (fun h => h.1.ne)

end
end G366022
```

## Normalized.lean

```lean
import Incidence

namespace G366022
noncomputable section
set_option linter.unusedSimpArgs false

def normalized0 (u v : R) : R := (p12 u v)⁻¹ • (v 1 • u - u 1 • v)
def normalized1 (u v : R) : R := (p12 u v)⁻¹ • (u 0 • v - v 0 • u)

theorem normalized0_chart (u v : R) (hn : p12 u v ≠ 0) :
    normalized0 u v = row0 (normalized0 u v 2) (normalized0 u v 3) := by
  ext i
  fin_cases i
  · change (p12 u v)⁻¹ * (v 1 * u 0 - u 1 * v 0) = 1
    rw [mul_comm (v 1), ← p12, inv_mul_cancel₀ hn]
  · change (p12 u v)⁻¹ * (v 1 * u 1 - u 1 * v 1) = 0
    ring
  · rfl
  · rfl

theorem normalized1_chart (u v : R) (hn : p12 u v ≠ 0) :
    normalized1 u v = row1 (normalized1 u v 2) (normalized1 u v 3) := by
  ext i
  fin_cases i
  · change (p12 u v)⁻¹ * (u 0 * v 0 - v 0 * u 0) = 0
    ring
  · change (p12 u v)⁻¹ * (u 0 * v 1 - v 0 * u 1) = 1
    rw [mul_comm (v 0), ← p12, inv_mul_cancel₀ hn]
  · rfl
  · rfl

theorem normalized_expand (u v : R) (hn : p12 u v ≠ 0) :
    u = u 0 • normalized0 u v + u 1 • normalized1 u v ∧
    v = v 0 • normalized0 u v + v 1 • normalized1 u v := by
  constructor <;> ext i <;>
    simp only [normalized0,normalized1,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  · calc
      u i = (p12 u v)⁻¹ * (p12 u v * u i) := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
      _ = _ := by unfold p12; ring
  · calc
      v i = (p12 u v)⁻¹ * (p12 u v * v i) := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
      _ = _ := by unfold p12; ring

theorem normalized_span (u v : R) (hn : p12 u v ≠ 0) :
    Graph (normalized0 u v 2) (normalized0 u v 3) (normalized1 u v 2) (normalized1 u v 3) =
      spanPair u v := by
  let u' := normalized0 u v
  let v' := normalized1 u v
  have hpair : spanPair u' v' = spanPair u v := by
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with he | he
      · rw [he]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (left_spanPair u v)) (Submodule.smul_mem _ _ (right_spanPair u v)))
      · rw [Set.mem_singleton_iff.mp he]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (right_spanPair u v)) (Submodule.smul_mem _ _ (left_spanPair u v)))
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with he | he
      · rw [he]
        exact mem_spanPair.mpr ⟨u 0,u 1,(normalized_expand u v hn).1.symm⟩
      · rw [Set.mem_singleton_iff.mp he]
        exact mem_spanPair.mpr ⟨v 0,v 1,(normalized_expand u v hn).2.symm⟩
  rw [graph_span, ← hpair]
  exact congrArg₂ spanPair (normalized0_chart u v hn).symm (normalized1_chart u v hn).symm

theorem stack_change (u v r s : R) (a b c d : ℝ) :
    (stack (a • u + b • v) (c • u + d • v) r s).det =
      (a*d-b*c) * (stack u v r s).det := by
  simp only [stack_det,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem normalized_chow (u v r s : R) (hn : p12 u v ≠ 0) :
    (stack u v r s).det = p12 u v *
      chow (normalized0 u v 2) (normalized0 u v 3)
        (normalized1 u v 2) (normalized1 u v 3) r s := by
  rw [chow, ← normalized0_chart u v hn, ← normalized1_chart u v hn]
  calc
    _ = (stack (u 0 • normalized0 u v + u 1 • normalized1 u v)
          (v 0 • normalized0 u v + v 1 • normalized1 u v) r s).det :=
      congrArg Matrix.det (congrArg₂ (fun x y => stack x y r s)
        (normalized_expand u v hn).1 (normalized_expand u v hn).2)
    _ = _ := stack_change _ _ _ _ _ _ _ _

theorem normalized_sign_no_reversal (a b c d : ℝ) :
    ¬ (∀ r s, Edge r s → chow a b c d r s * witnessChow true r s < 0) := by
  intro hh
  have hc := hh _ _ edge34
  norm_num [chow34,witnessChow34] at hc

theorem graph_coords_unique {a b c d a' b' c' d' : ℝ}
    (he : Graph a b c d = Graph a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h0 : row0 a b ∈ Graph a' b' c' d' := he ▸ (mem_graph.mpr (by simp [row0]))
  have h1 : row1 c d ∈ Graph a' b' c' d' := he ▸ (mem_graph.mpr (by simp [row1]))
  rw [mem_graph] at h0 h1
  simpa [row0,row1, and_assoc] using And.intro h0 h1

end
end G366022
```

## Chart.lean

```lean
import Normalized
import Mathlib.LinearAlgebra.Dimension.Free

namespace G366022
noncomputable section

theorem plane_basis (W : Submodule ℝ R) (hd : Module.finrank ℝ W = 2) :
    ∃ u v : R, LinearIndependent ℝ (![u,v] : Fin 2 → R) ∧ W = spanPair u v := by
  let b := Module.finBasisOfFinrankEq ℝ W hd
  let u : R := (b 0).val
  let v : R := (b 1).val
  have hl := b.linearIndependent.map' W.subtype (by simp)
  have he : (fun i : Fin 2 => W.subtype (b i)) = ![u,v] := by
    ext i j
    fin_cases i <;> rfl
  rw [Function.comp_def, he] at hl
  refine ⟨u,v,hl,le_antisymm ?_ ?_⟩
  · intro x hx
    let y : W := ⟨x,hx⟩
    apply mem_spanPair.mpr
    refine ⟨b.repr y 0,b.repr y 1,?_⟩
    have hs := congrArg Subtype.val (b.sum_repr y)
    rw [Fin.sum_univ_two] at hs
    exact hs
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with heq | heq
    · rw [heq]
      exact (b 0).property
    · rw [Set.mem_singleton_iff.mp heq]
      exact (b 1).property

abbrev Coords := ℝ × ℝ × ℝ × ℝ

def graphAt (p : Coords) : Submodule ℝ R := Graph p.1 p.2.1 p.2.2.1 p.2.2.2

theorem graphAt_injective : Function.Injective graphAt := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  obtain ⟨rfl,rfl,rfl,rfl⟩ := graph_coords_unique h
  rfl

theorem complement_graph (W : Submodule ℝ R) (hc : StabComplement W) :
    ∃! p : Coords, graphAt p = W := by
  obtain ⟨u,v,hli,hW⟩ := plane_basis W hc.1
  have hn := p12_ne_zero_of_away hli (hW ▸ hc.2.2)
  let p : Coords := (normalized0 u v 2, normalized0 u v 3, normalized1 u v 2, normalized1 u v 3)
  have hp : graphAt p = W := (normalized_span u v hn).trans hW.symm
  exact ⟨p,hp,fun q hq => graphAt_injective (hq.trans hp.symm)⟩

def ChartDomain := {p : Coords // StabComplement (graphAt p)}
def PlaneDomain := {W : Submodule ℝ R // StabComplement W}

def complementChart : ChartDomain ≃ PlaneDomain := by
  refine Equiv.ofBijective (fun p => ⟨graphAt p.val,p.property⟩) ⟨?_,?_⟩
  · intro p q he
    exact Subtype.ext (graphAt_injective (congrArg Subtype.val he))
  · intro W
    obtain ⟨p,hp,_⟩ := complement_graph W.val W.property
    exact ⟨⟨p,hp.symm ▸ W.property⟩,Subtype.ext hp⟩

theorem native_edge_span_iff (S : Submodule ℝ R) :
    (∃ F : Set R, ExposedEdgeFace F ∧ Submodule.span ℝ F = S) ↔
      ∃ r s : R, Edge r s ∧ spanPair r s = S := by
  constructor
  · rintro ⟨F,hF,hS⟩
    obtain ⟨r,s,he,rfl⟩ := (dim_one_face_iff F).mp hF
    exact ⟨r,s,he,(span_segment r s).symm.trans hS⟩
  · rintro ⟨r,s,he,hS⟩
    exact ⟨segment ℝ r s,(edge_iff_dim_one.mp he).2,(span_segment r s).trans hS⟩

theorem away_native_iff (W : Submodule ℝ R) :
    Away W ↔ ∀ F : Set R, ExposedEdgeFace F → Disjoint W (Submodule.span ℝ F) := by
  constructor
  · intro hw F hf
    obtain ⟨r,s,he,hs⟩ := (native_edge_span_iff (Submodule.span ℝ F)).mp ⟨F,hf,rfl⟩
    exact hs ▸ hw r s he
  · intro hw r s he
    simpa only [span_segment] using hw _ (edge_iff_dim_one.mp he).2

theorem chart_strict_same_iff (p q : Coords) :
    ((∀ r s, Edge r s → 0 < chow p.1 p.2.1 p.2.2.1 p.2.2.2 r s *
      chow q.1 q.2.1 q.2.2.1 q.2.2.2 r s) ∨
      (∀ r s, Edge r s → chow p.1 p.2.1 p.2.2.1 p.2.2.2 r s *
      chow q.1 q.2.1 q.2.2.1 q.2.2.2 r s < 0)) ↔
    (∀ r s, Edge r s → 0 < chow p.1 p.2.1 p.2.2.1 p.2.2.2 r s *
      chow q.1 q.2.1 q.2.2.1 q.2.2.2 r s) := by
  constructor
  · rintro (hp | hn)
    · exact hp
    · have h34 := hn _ _ edge34
      norm_num [chow34] at h34
  · exact Or.inl

end
end G366022
```

## Cone.lean

```lean
import Chart

namespace G366022
noncomputable section

def affineSum (w : Fin 8 → ℝ) : R := ∑ i, w i • g i

theorem affineSum_mem {w : Fin 8 → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    affineSum w ∈ P :=
  (convex_convexHull ℝ (Set.range g)).sum_mem (fun i _ => hw i) hs (fun i _ => g_mem i)

theorem mem_P_iff (x : R) :
    x ∈ P ↔ ∃ w : Fin 8 → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ affineSum w = x := by
  constructor
  · have hh : P ⊆ {y | ∃ w : Fin 8 → ℝ, (∀ i, 0 ≤ w i) ∧
        (∑ i, w i = 1) ∧ affineSum w = y} := by
      apply convexHull_min
      · rintro _ ⟨i,rfl⟩
        refine ⟨fun j => if j = i then 1 else 0,fun j => ?_,?_,?_⟩
        · by_cases hji : j = i <;> simp [hji]
        · simp
        · simp [affineSum,ite_smul]
      · rintro y ⟨u,hu,hus,rfl⟩ z ⟨v,hv,hvs,rfl⟩ a b ha hb hab
        refine ⟨fun i => a * u i + b * v i,fun i =>
          add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i)),?_,?_⟩
        · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hus, hvs, mul_one, hab]
        · simp only [affineSum,add_smul,mul_smul,Finset.sum_add_distrib,Finset.smul_sum]
    exact fun hx => hh hx
  · rintro ⟨w,hw,hs,rfl⟩
    exact affineSum_mem hw hs

def InPositiveCone (x : R) : Prop :=
  x ≠ 0 ∧ ∃ w : Fin 8 → ℝ, (∀ i, 0 ≤ w i) ∧ affineSum w = x

theorem h_affineSum (w : Fin 8 → ℝ) : h (affineSum w) = ∑ i, w i := by
  simp only [affineSum,map_sum,map_smul,h_g,smul_eq_mul,mul_one]

theorem cone_h_pos {x : R} (hx : InPositiveCone x) : 0 < h x := by
  obtain ⟨hn,w,hw,rfl⟩ := hx
  rw [h_affineSum]
  have he : ∃ i, 0 < w i := by
    by_contra! hh
    have hz (i : Fin 8) : w i = 0 := le_antisymm (hh i) (hw i)
    apply hn
    simp [affineSum,hz]
  obtain ⟨i,hi⟩ := he
  exact lt_of_lt_of_le hi (Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ i))

theorem cone_normalized_mem {x : R} (hx : InPositiveCone x) : (h x)⁻¹ • x ∈ P := by
  have hpos := cone_h_pos hx
  obtain ⟨_,w,hw,rfl⟩ := hx
  apply (mem_P_iff _).mpr
  refine ⟨fun i => (h (affineSum w))⁻¹ * w i,
    fun i => mul_nonneg (inv_nonneg.mpr hpos.le) (hw i),?_,?_⟩
  · rw [← Finset.mul_sum, ← h_affineSum, inv_mul_cancel₀ hpos.ne']
  · simp only [affineSum,mul_smul,Finset.smul_sum]

theorem chart_point_in_cone {x : R} (hp : x ∈ P) : InPositiveCone x := by
  refine ⟨?_,?_⟩
  · have hh := in_chart hp
    intro hz
    simp [hz] at hh
  · obtain ⟨w,hw,_,he⟩ := (mem_P_iff x).mp hp
    exact ⟨w,hw,he⟩

theorem stabs_iff_nonzero_cone (W : Submodule ℝ R) :
    Stabs W ↔ ∃ x : R, InPositiveCone x ∧ x ∈ W := by
  constructor
  · rintro ⟨x,hp,hw⟩
    exact ⟨x.val,chart_point_in_cone hp,hw⟩
  · rintro ⟨x,hp,hw⟩
    let y : H := ⟨(h x)⁻¹ • x, by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (cone_h_pos hp).ne']⟩
    exact ⟨y,cone_normalized_mem hp, W.smul_mem _ hw⟩

end
end G366022
```

## Signs.lean

```lean
import Cone

namespace G366022
noncomputable section

def EdgeIndex := {ij : Fin 8 × Fin 8 // Edge (g ij.1) (g ij.2)}

instance : Finite EdgeIndex := by
  unfold EdgeIndex
  infer_instance

def graphChow (p : Coords) (r s : R) : ℝ :=
  chow p.1 p.2.1 p.2.2.1 p.2.2.2 r s

theorem chartChow_ne_zero (p : ChartDomain) {r s : R} (he : Edge r s) :
    graphChow p.val r s ≠ 0 :=
  (chow_ne_zero_iff _ _ _ _ he).mpr (p.property.2.2 r s he)

def edgeSign (p : ChartDomain) (ij : EdgeIndex) : Bool :=
  decide (0 < graphChow p.val (g ij.val.1) (g ij.val.2))

def RealizedSigns := Set.range edgeSign

theorem finite_realized_signs : RealizedSigns.Finite :=
  Set.toFinite _

theorem chart_sign_equal (p q : ChartDomain) :
    edgeSign p = edgeSign q ↔ ∀ r s, Edge r s →
      0 < graphChow p.val r s * graphChow q.val r s := by
  constructor
  · intro h r s he
    obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := edge_generators he
    have hbool := congrFun h (⟨(i,j),he⟩ : EdgeIndex)
    change decide (0 < graphChow p.val (g i) (g j)) =
      decide (0 < graphChow q.val (g i) (g j)) at hbool
    by_cases hp : 0 < graphChow p.val (g i) (g j)
    · have hq : 0 < graphChow q.val (g i) (g j) := by simpa [hp,eq_comm] using hbool
      exact mul_pos hp hq
    · have hq : ¬ 0 < graphChow q.val (g i) (g j) := by simpa [hp,eq_comm] using hbool
      exact mul_pos_of_neg_of_neg
        (lt_of_le_of_ne (le_of_not_gt hp) (chartChow_ne_zero p he))
        (lt_of_le_of_ne (le_of_not_gt hq) (chartChow_ne_zero q he))
  · intro hh
    funext ij
    obtain ⟨⟨i,j⟩,he⟩ := ij
    rcases mul_pos_iff.mp (hh _ _ he) with ⟨hp,hq⟩ | ⟨hp,hq⟩
    · simp [edgeSign,hp,hq]
    · simp [edgeSign,not_lt_of_gt hp,not_lt_of_gt hq]

def chartWitness (plus : Bool) : ChartDomain :=
  ⟨(1,signedT plus,signedT plus,t^2/2),graph_witness_stab_complement plus⟩

theorem witness_sign_equal : edgeSign (chartWitness true) = edgeSign (chartWitness false) :=
  (chart_sign_equal _ _).mpr fun _ _ he => all_edge_product_pos he

theorem witness_b_pos : 0 < (chartWitness true).val.2.1 := by
  change 0 < t
  norm_num [t]

theorem witness_b_neg : (chartWitness false).val.2.1 < 0 := by
  change -t < 0
  norm_num [t]

theorem same_sign_b_ne_zero (p : ChartDomain)
    (hs : edgeSign p = edgeSign (chartWitness true)) : p.val.2.1 ≠ 0 := by
  apply chart_b_ne_zero p.val.1 _ p.val.2.2.1 p.val.2.2.2
  exact (chart_sign_equal p (chartWitness true)).mp hs

theorem continuous_graphChow (r s : R) : Continuous (fun p : Coords => graphChow p r s) := by
  have ha : Continuous (fun p : Coords => p.1) := continuous_fst
  have hb : Continuous (fun p : Coords => p.2.1) := continuous_fst.comp continuous_snd
  have hc : Continuous (fun p : Coords => p.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hd : Continuous (fun p : Coords => p.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hx (x : R) : Continuous (fun p : Coords => qx p.1 p.2.2.1 x) := by
    unfold qx
    exact (continuous_const.sub (ha.mul continuous_const)).sub (hc.mul continuous_const)
  have hy (x : R) : Continuous (fun p : Coords => qy p.2.1 p.2.2.2 x) := by
    unfold qy
    exact (continuous_const.sub (hb.mul continuous_const)).sub (hd.mul continuous_const)
  simp only [graphChow,chow_quotient,quotientDet]
  exact ((hx r).mul (hy s)).sub ((hy r).mul (hx s))

end
end G366022
```

## ChartTopology.lean

```lean
import Signs
import Mathlib.Topology.Order.IntermediateValue

namespace G366022
noncomputable section

instance : TopologicalSpace ChartDomain := by
  unfold ChartDomain
  infer_instance

theorem continuous_b : Continuous (fun p : ChartDomain => p.val.2.1) :=
  continuous_fst.comp (continuous_snd.comp continuous_subtype_val)

private theorem same_strict_sign_of_preconnected {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) {f : X → ℝ} (hf : Continuous f)
    (hn : ∀ x ∈ S, f x ≠ 0) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    0 < f x * f y := by
  have ho := (hS.image f hf.continuousOn).ordConnected
  have hfx : f x ∈ f '' S := ⟨x,hx,rfl⟩
  have hfy : f y ∈ f '' S := ⟨y,hy,rfl⟩
  by_cases hxpos : 0 < f x
  · by_cases hypos : 0 < f y
    · exact mul_pos hxpos hypos
    · have h0 : (0 : ℝ) ∈ f '' S := ho.out hfy hfx ⟨le_of_not_gt hypos,hxpos.le⟩
      obtain ⟨z,hz,hzero⟩ := h0
      exact (hn z hz hzero).elim
  · by_cases hypos : 0 < f y
    · have h0 : (0 : ℝ) ∈ f '' S := ho.out hfx hfy ⟨le_of_not_gt hxpos,hypos.le⟩
      obtain ⟨z,hz,hzero⟩ := h0
      exact (hn z hz hzero).elim
    · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt hxpos) (hn x hx))
        (lt_of_le_of_ne (le_of_not_gt hypos) (hn y hy))

theorem preconnected_chart_sign_const {S : Set ChartDomain} (hS : IsPreconnected S)
    {p q : ChartDomain} (hp : p ∈ S) (hq : q ∈ S) : edgeSign p = edgeSign q := by
  refine (chart_sign_equal p q).mpr fun r s he => ?_
  exact same_strict_sign_of_preconnected hS
    ((continuous_graphChow r s).comp continuous_subtype_val)
    (fun x _ => chartChow_ne_zero x he) hp hq

theorem no_preconnected_chart_witnesses {S : Set ChartDomain} (hS : IsPreconnected S)
    (hp : chartWitness true ∈ S) (hm : chartWitness false ∈ S) : False := by
  have hn : ∀ x ∈ S, x.val.2.1 ≠ 0 := fun x hx =>
    same_sign_b_ne_zero x (preconnected_chart_sign_const hS hx hp)
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos witness_b_pos.le witness_b_neg.le))
    (same_strict_sign_of_preconnected hS continuous_b hn hp hm)

theorem chart_witnesses_components_ne :
    connectedComponent (chartWitness true) ≠ connectedComponent (chartWitness false) := by
  intro he
  exact no_preconnected_chart_witnesses isConnected_connectedComponent.isPreconnected
    mem_connectedComponent (he ▸ mem_connectedComponent)

end
end G366022
```

## Plucker.lean

```lean
import ChartTopology
import Cone

namespace G366022
noncomputable section

def minor (u v : R) (i j : Fin 4) : ℝ := u i * v j - u j * v i

def minors (u v : R) : Fin 6 → ℝ :=
  ![minor u v 0 1, minor u v 0 2, minor u v 0 3,
    minor u v 1 2, minor u v 1 3, minor u v 2 3]

theorem minor_expand (u v : R) (a b c d : ℝ) (i j : Fin 4) :
    minor (a • u + b • v) (c • u + d • v) i j =
      (a*d-b*c) * minor u v i j := by
  simp only [minor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem minors_expand (u v : R) (a b c d : ℝ) :
    minors (a • u + b • v) (c • u + d • v) = (a*d-b*c) • minors u v := by
  funext k
  fin_cases k <;> exact minor_expand u v a b c d _ _

theorem minor_scale_of_minors {u v w z : R} (t : ℝ)
    (h : minors w z = t • minors u v) (i j : Fin 4) :
    minor w z i j = t * minor u v i j := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  change minor w z 0 1 = t * minor u v 0 1 at h0
  change minor w z 0 2 = t * minor u v 0 2 at h1
  change minor w z 0 3 = t * minor u v 0 3 at h2
  change minor w z 1 2 = t * minor u v 1 2 at h3
  change minor w z 1 3 = t * minor u v 1 3 at h4
  change minor w z 2 3 = t * minor u v 2 3 at h5
  fin_cases i <;> fin_cases j <;> dsimp at * <;> unfold minor at * <;> linarith

theorem exists_minor_ne {u v : R} (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R)) :
    ∃ i j, minor u v i j ≠ 0 := by
  obtain ⟨hv, hu⟩ := linearIndependent_fin2.mp hl
  change v ≠ 0 at hv
  by_contra! h
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! H
    exact hv (funext H)
  apply hu (u i / v i)
  change (u i / v i) • v = u
  funext j
  change (u i / v i) * v j = u j
  rw [div_mul_eq_mul_div, div_eq_iff hi]
  exact sub_eq_zero.mp (h i j)

theorem minors_ne_zero {u v : R} (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R)) :
    minors u v ≠ 0 := by
  obtain ⟨i,j,hij⟩ := exists_minor_ne hl
  intro h
  have hs := minor_scale_of_minors (u := u) (v := v) (w := u) (z := v)
    0 (by simpa using h) i j
  exact hij (by simpa using hs)

theorem spanPair_eq_of_minor_scale {u v w z : R} {t : ℝ} (ht : t ≠ 0)
    (h : minors w z = t • minors u v)
    (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R))
    (hr : LinearIndependent ℝ (![w,z] : Fin 2 → R)) :
    spanPair u v = spanPair w z := by
  have step : ∀ (u v w z : R) (t : ℝ), t ≠ 0 →
      LinearIndependent ℝ (![u,v] : Fin 2 → R) →
      minors w z = t • minors u v → spanPair w z ≤ spanPair u v := by
    intro U V W Z s hs hli hm
    obtain ⟨i,j,hij⟩ := exists_minor_ne hli
    have H := minor_scale_of_minors s hm
    have member (x : R) (hx : ∀ k, minor W Z i j * x k -
        minor W Z i k * x j + minor W Z j k * x i = 0) : x ∈ spanPair U V := by
      apply mem_spanPair.mpr
      refine ⟨(x i * V j - x j * V i) / minor U V i j,
        (U i * x j - U j * x i) / minor U V i j, ?_⟩
      funext k
      change (x i * V j - x j * V i) / minor U V i j * U k +
        (U i * x j - U j * x i) / minor U V i j * V k = x k
      have he := hx k
      rw [H,H,H] at he
      have hz : minor U V i j * x k - minor U V i k * x j +
          minor U V j k * x i = 0 := by
        apply (mul_eq_zero.mp (_ : s * _ = 0)).resolve_left hs
        linear_combination he
      simp only [div_mul_eq_mul_div, ← add_div]
      rw [div_eq_iff hij]
      unfold minor at hz ⊢
      linear_combination -hz
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hW | hZ
    · subst x
      apply member
      intro k
      unfold minor
      ring
    · rw [Set.mem_singleton_iff] at hZ
      subst x
      apply member
      intro k
      unfold minor
      ring
  apply le_antisymm _ (step u v w z t ht hl h)
  apply step w z u v t⁻¹ (inv_ne_zero ht) hr
  rw [h, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem minors_scale_of_spanPair_eq {u v w z : R}
    (h : spanPair w z = spanPair u v)
    (hr : LinearIndependent ℝ (![w,z] : Fin 2 → R)) :
    ∃ t : ℝ, t ≠ 0 ∧ minors w z = t • minors u v := by
  have hw : w ∈ spanPair w z := mem_spanPair.mpr ⟨1,0,by simp⟩
  have hz : z ∈ spanPair w z := mem_spanPair.mpr ⟨0,1,by simp⟩
  rw [h] at hw hz
  obtain ⟨a,b,ha⟩ := mem_spanPair.mp hw
  obtain ⟨c,d,hc⟩ := mem_spanPair.mp hz
  have hm : minors w z = (a*d-b*c) • minors u v := by
    rw [← ha, ← hc]
    exact minors_expand u v a b c d
  refine ⟨_,?_,hm⟩
  intro hn
  exact minors_ne_zero hr (by simpa [hn] using hm)

end
end G366022
```

## Projective.lean

```lean
import Plucker
import Mathlib.Topology.Constructions
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace G366022
noncomputable section

abbrev Six := Fin 6 → ℝ
abbrev NonzeroSix := {x : Six // x ≠ 0}

def scalarSetoid : Setoid NonzeroSix where
  r x y := ∃ t : ℝ, t ≠ 0 ∧ y.val = t • x.val
  iseqv := by
    constructor
    · intro x
      exact ⟨1, one_ne_zero, (one_smul ℝ x.val).symm⟩
    · rintro x y ⟨t,ht,h⟩
      refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
      rw [h, smul_smul, inv_mul_cancel₀ ht, one_smul]
    · rintro x y z ⟨t,ht,h⟩ ⟨s,hs,k⟩
      exact ⟨s*t, mul_ne_zero hs ht, by rw [k,h,smul_smul]⟩

def ProjectiveSix := Quotient scalarSetoid

instance : TopologicalSpace ProjectiveSix := by
  unfold ProjectiveSix
  infer_instance

def project (x : NonzeroSix) : ProjectiveSix := @Quotient.mk' _ scalarSetoid x

theorem project_quotient : Topology.IsQuotientMap project :=
  @isQuotientMap_quotient_mk' _ _ scalarSetoid

theorem project_eq_iff (x y : NonzeroSix) :
    project x = project y ↔ ∃ t : ℝ, t ≠ 0 ∧ y.val = t • x.val :=
  ⟨fun h => @Quotient.exact _ scalarSetoid _ _ h,
    fun h => @Quotient.sound _ scalarSetoid _ _ h⟩

def projectMinor (u v : R) (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R)) :
    ProjectiveSix := project ⟨minors u v, minors_ne_zero hl⟩

abbrev RealGr := {W : Submodule ℝ R // Module.finrank ℝ W = 2}

def frame (W : RealGr) : R × R :=
  ((plane_basis W.val W.property).choose, (plane_basis W.val W.property).choose_spec.choose)

theorem frame_spec (W : RealGr) :
    LinearIndependent ℝ (![ (frame W).1, (frame W).2 ] : Fin 2 → R) ∧
      W.val = spanPair (frame W).1 (frame W).2 :=
  (plane_basis W.val W.property).choose_spec.choose_spec

def plucker (W : RealGr) : ProjectiveSix :=
  projectMinor (frame W).1 (frame W).2 (frame_spec W).1

theorem plucker_of_span (W : RealGr) (u v : R)
    (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R)) (hw : W.val = spanPair u v) :
    plucker W = projectMinor u v hl := by
  unfold plucker projectMinor
  apply (project_eq_iff _ _).2
  exact minors_scale_of_spanPair_eq (hw.symm.trans (frame_spec W).2) hl

theorem plucker_injective : Function.Injective plucker := by
  intro W Z he
  unfold plucker projectMinor at he
  obtain ⟨t,ht,hm⟩ := (project_eq_iff _ _).1 he
  exact Subtype.ext ((frame_spec W).2.trans
    ((spanPair_eq_of_minor_scale ht hm (frame_spec W).1 (frame_spec Z).1).trans
      (frame_spec Z).2.symm))

theorem spanPair_rank {u v : R} (hl : LinearIndependent ℝ (![u,v] : Fin 2 → R)) :
    Module.finrank ℝ (spanPair u v) = 2 := by
  have he : Set.range (![u,v] : Fin 2 → R) = {u,v} := by
    ext x
    simp [or_comm]
  unfold spanPair
  rw [← he, finrank_span_eq_card hl, Fintype.card_fin]

theorem independent_of_minors_ne {u v : R} (hn : minors u v ≠ 0) :
    LinearIndependent ℝ (![u,v] : Fin 2 → R) := by
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ t : ℝ, t • v ≠ u
  constructor
  · intro hv
    subst v
    apply hn
    funext i
    fin_cases i <;> simp [minors, minor]
  · intro t ht
    subst u
    apply hn
    funext i
    fin_cases i <;> simp [minors, minor] <;> ring

def Decomposable (p : ProjectiveSix) : Prop :=
  ∃ u v : R, ∃ hz : minors u v ≠ 0, project ⟨minors u v,hz⟩ = p

theorem plucker_range : Set.range plucker = {p | Decomposable p} := by
  ext p
  constructor
  · rintro ⟨W,rfl⟩
    exact ⟨_,_,minors_ne_zero (frame_spec W).1,rfl⟩
  · rintro ⟨u,v,hz,rfl⟩
    have hl := independent_of_minors_ne hz
    exact ⟨⟨spanPair u v,spanPair_rank hl⟩,plucker_of_span _ u v hl rfl⟩

instance realGrTopology : TopologicalSpace RealGr :=
  TopologicalSpace.induced plucker inferInstance

theorem plucker_embedding : Topology.IsEmbedding plucker :=
  ⟨⟨rfl⟩,plucker_injective⟩

end
end G366022
```

## ProjectiveChart.lean

```lean
import Projective

namespace G366022
noncomputable section

def InFirstPatch (p : ProjectiveSix) : Prop :=
  Quotient.lift (fun x : NonzeroSix => x.val 0 ≠ 0) (by
    rintro x y ⟨t,ht,h⟩
    apply propext
    rw [h]
    change x.val 0 ≠ 0 ↔ t * x.val 0 ≠ 0
    exact ⟨mul_ne_zero ht, fun hne hx => hne (by rw [hx,mul_zero])⟩) p

theorem firstPatch_open : IsOpen {p : ProjectiveSix | InFirstPatch p} := by
  apply project_quotient.isCoinducing.isOpen_preimage.mp
  change IsOpen {x : NonzeroSix | x.val 0 ≠ 0}
  exact isOpen_ne_fun ((continuous_apply (0 : Fin 6)).comp continuous_subtype_val)
    continuous_const

abbrev FirstPatch := {p : ProjectiveSix // InFirstPatch p}
abbrev NormalizedSix := {x : Six // x 0 = 1}

def projectRatios (p : ProjectiveSix) : Six :=
  Quotient.lift (fun x : NonzeroSix => fun i => x.val i / x.val 0) (by
    rintro x y ⟨t,ht,h⟩
    rw [h]
    funext i
    change x.val i / x.val 0 = (t * x.val i) / (t * x.val 0)
    rw [mul_div_mul_left _ _ ht]) p

theorem projectRatios_continuous : Continuous (fun p : FirstPatch => projectRatios p.val) := by
  apply (project_quotient.restrictPreimage_isOpen firstPatch_open).continuous_iff.mpr
  apply continuous_pi
  intro i
  let X := {x : NonzeroSix // x ∈ project ⁻¹' {p | InFirstPatch p}}
  change Continuous (fun x : X => x.val.val i / x.val.val 0)
  have h (j : Fin 6) : Continuous (fun x : X => x.val.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (h i).div (h 0) (fun x => x.property)

theorem projectRatios_first (p : ProjectiveSix) (hp : InFirstPatch p) :
    projectRatios p 0 = 1 := by
  induction p using Quotient.inductionOn with
  | _ x =>
    change x.val 0 / x.val 0 = 1
    exact div_self hp

def normalizedProject (x : NormalizedSix) : FirstPatch :=
  ⟨project ⟨x.val, fun h => by
      have h0 := congrFun h 0
      exact one_ne_zero (x.property.symm.trans h0)⟩,
    fun h => one_ne_zero (x.property.symm.trans h)⟩

def firstPatchHomeomorph : FirstPatch ≃ₜ NormalizedSix where
  toFun p := ⟨projectRatios p.val, projectRatios_first p.val p.property⟩
  invFun := normalizedProject
  left_inv := by
    rintro ⟨p,hp⟩
    apply Subtype.ext
    induction p using Quotient.inductionOn with
    | _ x =>
      apply (project_eq_iff _ _).mpr
      refine ⟨x.val 0, hp, ?_⟩
      funext i
      change x.val i = x.val 0 * (x.val i / x.val 0)
      field_simp [show x.val 0 ≠ 0 from hp]
  right_inv := by
    intro x
    apply Subtype.ext
    funext i
    change x.val i / x.val 0 = x.val i
    rw [x.property, div_one]
  continuous_toFun := continuous_induced_rng.2 projectRatios_continuous
  continuous_invFun := continuous_induced_rng.2
    (project_quotient.continuous.comp (continuous_induced_rng.2 continuous_subtype_val))

end
end G366022
```

## NativeChart.lean

```lean
import ProjectiveChart

namespace G366022
noncomputable section

def NativeStabs (W : Submodule ℝ R) : Prop :=
  ∃ x : R, InPositiveCone x ∧ x ∈ W

def NativeAway (W : Submodule ℝ R) : Prop :=
  ∀ F : Set R, ExposedEdgeFace F → Disjoint W (Submodule.span ℝ F)

abbrev NativeDomain := {W : RealGr // NativeStabs W.val ∧ NativeAway W.val}

def nativePlaneEquiv : NativeDomain ≃ PlaneDomain where
  toFun W := ⟨W.val.val, W.val.property,
    (stabs_iff_nonzero_cone _).mpr W.property.1, (away_native_iff _).mpr W.property.2⟩
  invFun W := ⟨⟨W.val, W.property.1⟩,
    (stabs_iff_nonzero_cone _).mp W.property.2.1, (away_native_iff _).mp W.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def chartNativeEquiv : ChartDomain ≃ NativeDomain :=
  complementChart.trans nativePlaneEquiv.symm

def nativePatch (W : NativeDomain) : FirstPatch :=
  ⟨plucker W.val, by
    change p12 (frame W.val).1 (frame W.val).2 ≠ 0
    apply p12_ne_zero_of_away (frame_spec W.val).1
    rw [← (frame_spec W.val).2]
    exact (away_native_iff _).mpr W.property.2⟩

theorem nativePatch_continuous : Continuous nativePatch :=
  continuous_induced_rng.2 (plucker_embedding.continuous.comp continuous_subtype_val)

def graphMinors (p : Coords) : Six :=
  ![1,p.2.2.1,p.2.2.2,-p.1,-p.2.1,p.1*p.2.2.2-p.2.1*p.2.2.1]

theorem graphMinors_eq (p : Coords) :
    minors (row0 p.1 p.2.1) (row1 p.2.2.1 p.2.2.2) = graphMinors p := by
  funext i
  fin_cases i <;> simp [minors, minor, row0, row1, graphMinors]

theorem graphMinors_continuous : Continuous graphMinors := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [graphMinors] <;> fun_prop

def normalizedGraph (p : ChartDomain) : NormalizedSix :=
  ⟨graphMinors p.val, rfl⟩

theorem normalizedGraph_continuous : Continuous normalizedGraph :=
  continuous_induced_rng.2 (graphMinors_continuous.comp continuous_subtype_val)

theorem chartNative_plucker (p : ChartDomain) :
    plucker (chartNativeEquiv p).val = (normalizedProject (normalizedGraph p)).val := by
  change plucker (chartNativeEquiv p).val = project _
  rw [plucker_of_span (chartNativeEquiv p).val _ _
    (graph_basis p.val.1 p.val.2.1 p.val.2.2.1 p.val.2.2.2)
    (graph_span p.val.1 p.val.2.1 p.val.2.2.1 p.val.2.2.2)]
  apply congrArg project
  exact Subtype.ext (graphMinors_eq p.val)

theorem nativePatch_on_chart (p : ChartDomain) :
    nativePatch (chartNativeEquiv p) = firstPatchHomeomorph.symm (normalizedGraph p) :=
  Subtype.ext (chartNative_plucker p)

def extractGraph (q : NormalizedSix) : Coords :=
  (-q.val 3,-q.val 4,q.val 1,q.val 2)

theorem extractGraph_continuous : Continuous extractGraph := by
  have hc (i : Fin 6) : Continuous (fun q : NormalizedSix => q.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact (hc 3).neg.prodMk ((hc 4).neg.prodMk ((hc 1).prodMk (hc 2)))

theorem extractGraph_normalized (p : ChartDomain) : extractGraph (normalizedGraph p) = p.val := by
  simp [extractGraph, normalizedGraph, graphMinors]

theorem chartNative_continuous : Continuous chartNativeEquiv := by
  apply continuous_induced_rng.2
  apply continuous_induced_rng.2
  have he : (fun p : ChartDomain => plucker (chartNativeEquiv p).val) =
      (fun p => (normalizedProject (normalizedGraph p)).val) := funext chartNative_plucker
  change Continuous (fun p : ChartDomain => plucker (chartNativeEquiv p).val)
  rw [he]
  exact continuous_subtype_val.comp
    (firstPatchHomeomorph.symm.continuous.comp normalizedGraph_continuous)

theorem nativeChart_continuous : Continuous chartNativeEquiv.symm := by
  apply continuous_induced_rng.2
  have he : (fun W : NativeDomain => (chartNativeEquiv.symm W).val) =
      extractGraph ∘ firstPatchHomeomorph ∘ nativePatch := by
    funext W
    obtain ⟨p,rfl⟩ := chartNativeEquiv.surjective W
    simp only [Function.comp_apply, Equiv.symm_apply_apply, nativePatch_on_chart,
      Homeomorph.apply_symm_apply, extractGraph_normalized]
  change Continuous (fun W : NativeDomain => (chartNativeEquiv.symm W).val)
  rw [he]
  exact extractGraph_continuous.comp (firstPatchHomeomorph.continuous.comp nativePatch_continuous)

def nativeChartHomeomorph : ChartDomain ≃ₜ NativeDomain where
  toEquiv := chartNativeEquiv
  continuous_toFun := chartNative_continuous
  continuous_invFun := nativeChart_continuous

theorem nativeChart_agrees (p : ChartDomain) :
    nativePlaneEquiv (nativeChartHomeomorph p) = complementChart p := by
  exact nativePlaneEquiv.apply_symm_apply _

end
end G366022
```

## NativeChow.lean

```lean
import Projective

namespace G366022
noncomputable section

-- Source dual coordinates are the row minors. Primal coordinates are signed
-- complementary minors in the order 12, 13, 14, 23, 24, 34.
def primalMinors (u v : R) : Six :=
  ![minor u v 2 3, -minor u v 1 3, minor u v 1 2,
    minor u v 0 3, -minor u v 0 2, minor u v 0 1]

def sourceChow (u v r s : R) : ℝ :=
  ∑ i : Fin 6, minors r s i * primalMinors u v i

theorem sourceChow_det (u v r s : R) : sourceChow u v r s = (stack u v r s).det := by
  rw [stack_det]
  simp [sourceChow, Fin.sum_univ_succ, primalMinors, minors, minor]
  ring

theorem sourceChow_plane_scale {u v w z : R} {t : ℝ}
    (ht : minors w z = t • minors u v) (r s : R) :
    sourceChow w z r s = t * sourceChow u v r s := by
  have hm := minor_scale_of_minors t ht
  simp only [sourceChow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [primalMinors, hm] <;> ring

theorem sourceChow_edge_scale {r s a b : R} {t : ℝ}
    (ht : minors a b = t • minors r s) (u v : R) :
    sourceChow u v a b = t * sourceChow u v r s := by
  simp only [sourceChow, Finset.mul_sum, ht, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def NativeEdgeSpan :=
  {S : Submodule ℝ R // ∃ F : Set R, ExposedEdgeFace F ∧ Submodule.span ℝ F = S}

def edgeSpanOfIndex (ij : EdgeIndex) : NativeEdgeSpan :=
  ⟨spanPair (g ij.val.1) (g ij.val.2), (native_edge_span_iff _).mpr ⟨_,_,ij.property,rfl⟩⟩

theorem edgeSpanOfIndex_surjective : Function.Surjective edgeSpanOfIndex := by
  intro S
  obtain ⟨r,s,he,hs⟩ := (native_edge_span_iff _).mp S.property
  obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := edge_generators he
  exact ⟨⟨(i,j),he⟩,Subtype.ext hs⟩

instance : Finite NativeEdgeSpan := Finite.of_surjective _ edgeSpanOfIndex_surjective

def edgeChoice (S : NativeEdgeSpan) : EdgeIndex :=
  (edgeSpanOfIndex_surjective S).choose

theorem edgeChoice_spec (S : NativeEdgeSpan) : edgeSpanOfIndex (edgeChoice S) = S :=
  (edgeSpanOfIndex_surjective S).choose_spec

def indexedChow (u v : R) (ij : EdgeIndex) : ℝ :=
  sourceChow u v (g ij.val.1) (g ij.val.2)

theorem indexedChow_scale_of_same_span {i j : EdgeIndex}
    (he : edgeSpanOfIndex i = edgeSpanOfIndex j) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ u v : R, indexedChow u v i = t * indexedChow u v j := by
  have h : spanPair (g i.val.1) (g i.val.2) = spanPair (g j.val.1) (g j.val.2) :=
    congrArg Subtype.val he
  obtain ⟨t,ht,hm⟩ := minors_scale_of_spanPair_eq h (edge_basis i.property)
  exact ⟨t,ht,fun u v => sourceChow_edge_scale hm u v⟩

def spanChow (u v : R) (S : NativeEdgeSpan) : ℝ :=
  indexedChow u v (edgeChoice S)

theorem spanChow_basis_scale {u v w z : R}
    (h : spanPair w z = spanPair u v) (hl : LinearIndependent ℝ (![w,z] : Fin 2 → R)) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ S, spanChow w z S = t * spanChow u v S := by
  obtain ⟨t,ht,hm⟩ := minors_scale_of_spanPair_eq h hl
  exact ⟨t,ht,fun S => sourceChow_plane_scale hm _ _⟩

end
end G366022
```

## NativeSigns.lean

```lean
import NativeChart
import NativeChow

namespace G366022
noncomputable section

def strictBit (x : ℝ) : Bool := decide (0 < x)

theorem strictBit_mul_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    strictBit (t*x) = strictBit x := by
  have he := mul_pos_iff_of_pos_left (b := x) ht
  by_cases h : 0 < x
  · simp [strictBit, h, he.mpr h]
  · have hm : ¬ 0 < t*x := fun hp => h (he.mp hp)
    simp [strictBit, h, hm]

theorem strictBit_mul_neg {t x : ℝ} (ht : t < 0) (hx : x ≠ 0) :
    strictBit (t*x) = !(strictBit x) := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have hm := mul_pos_of_neg_of_neg ht hn
    simp [strictBit, hm, not_lt_of_ge hn.le]
  · have hm := mul_neg_of_neg_of_pos ht hp
    simp [strictBit, hp, not_lt_of_ge hm.le]

theorem strictBit_scale_eq_iff {t x y : ℝ} (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    strictBit (t*x) = strictBit (t*y) ↔ strictBit x = strictBit y := by
  rcases lt_or_gt_of_ne ht with hn | hp
  · rw [strictBit_mul_neg hn hx, strictBit_mul_neg hn hy]
    cases strictBit x <;> cases strictBit y <;> decide
  · rw [strictBit_mul_pos hp, strictBit_mul_pos hp]

abbrev SpanBits := NativeEdgeSpan → Bool

def flipBits (f : SpanBits) : SpanBits := fun i => !(f i)

theorem flipBits_involutive (f : SpanBits) : flipBits (flipBits f) = f := by
  funext i
  simp [flipBits]

def signSetoid : Setoid SpanBits where
  r f g := f = g ∨ f = flipBits g
  iseqv := by
    constructor
    · intro f
      exact Or.inl rfl
    · rintro f g (rfl | hf)
      · exact Or.inl rfl
      · exact Or.inr (by rw [hf, flipBits_involutive])
    · rintro f g h (rfl | hfg) (rfl | hgh)
      · exact Or.inl rfl
      · exact Or.inr hgh
      · exact Or.inr hfg
      · exact Or.inl (by rw [hfg,hgh,flipBits_involutive])

def ProjectiveSigns := Quotient signSetoid

instance : Finite ProjectiveSigns := Finite.of_surjective _ (@Quotient.mk_surjective _ signSetoid)

def signClass (f : SpanBits) : ProjectiveSigns := Quotient.mk signSetoid f

theorem signClass_eq_iff (f g : SpanBits) :
    signClass f = signClass g ↔ f = g ∨ f = flipBits g :=
  ⟨fun h => @Quotient.exact _ signSetoid _ _ h,
    fun h => @Quotient.sound _ signSetoid _ _ h⟩

theorem class_scale {f g : NativeEdgeSpan → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hn : ∀ S, f S ≠ 0) (h : ∀ S, g S = t * f S) :
    signClass (strictBit ∘ g) = signClass (strictBit ∘ f) := by
  apply (signClass_eq_iff _ _).mpr
  rcases lt_or_gt_of_ne ht with ht | ht
  · right
    funext S
    exact (congrArg strictBit (h S)).trans (strictBit_mul_neg ht (hn S))
  · left
    funext S
    exact (congrArg strictBit (h S)).trans (strictBit_mul_pos ht (f S))

def nativeEval (W : NativeDomain) : NativeEdgeSpan → ℝ :=
  spanChow (frame W.val).1 (frame W.val).2

theorem nativeEval_ne_zero (W : NativeDomain) (S : NativeEdgeSpan) :
    nativeEval W S ≠ 0 := by
  let i := edgeChoice S
  change sourceChow (frame W.val).1 (frame W.val).2 (g i.val.1) (g i.val.2) ≠ 0
  rw [sourceChow_det, det_ne_zero_iff_disjoint _ _ _ _ (frame_spec W.val).1 (edge_basis i.property),
    ← (frame_spec W.val).2]
  change Disjoint W.val.val (edgeSpanOfIndex i).val
  rw [edgeChoice_spec]
  obtain ⟨F,hF,hS⟩ := S.property
  rw [← hS]
  exact W.property.2 F hF

def nativeSign (W : NativeDomain) : ProjectiveSigns :=
  signClass (strictBit ∘ nativeEval W)

theorem nativeSign_of_basis (W : NativeDomain) (u v : R)
    (huv : LinearIndependent ℝ (![u,v] : Fin 2 → R)) (hW : W.val.val = spanPair u v) :
    signClass (strictBit ∘ spanChow u v) = nativeSign W := by
  obtain ⟨t,ht,h⟩ := spanChow_basis_scale (hW.symm.trans (frame_spec W.val).2) huv
  exact class_scale ht (nativeEval_ne_zero W) h

def chartSpanEval (p : ChartDomain) : NativeEdgeSpan → ℝ :=
  spanChow (row0 p.val.1 p.val.2.1) (row1 p.val.2.2.1 p.val.2.2.2)

theorem graphIndexChow (p : ChartDomain) (i : EdgeIndex) :
    indexedChow (row0 p.val.1 p.val.2.1) (row1 p.val.2.2.1 p.val.2.2.2) i =
      graphChow p.val (g i.val.1) (g i.val.2) :=
  sourceChow_det _ _ _ _

theorem chartSpanEval_eq (p : ChartDomain) (S : NativeEdgeSpan) :
    chartSpanEval p S = graphChow p.val (g (edgeChoice S).val.1) (g (edgeChoice S).val.2) :=
  graphIndexChow p (edgeChoice S)

theorem chartSpanEval_ne_zero (p : ChartDomain) (S : NativeEdgeSpan) :
    chartSpanEval p S ≠ 0 := by
  rw [chartSpanEval_eq]
  exact chartChow_ne_zero p (edgeChoice S).property

def chartSpanBits (p : ChartDomain) : SpanBits := strictBit ∘ chartSpanEval p

theorem chartSpanBits_eval (p : ChartDomain) (S : NativeEdgeSpan) :
    chartSpanBits p S = edgeSign p (edgeChoice S) := by
  unfold chartSpanBits
  rw [Function.comp_apply, chartSpanEval_eq]
  rfl

theorem chartSpanBits_eq_iff (p q : ChartDomain) :
    chartSpanBits p = chartSpanBits q ↔ edgeSign p = edgeSign q := by
  constructor
  · intro he
    funext i
    obtain ⟨t,ht,hm⟩ := indexedChow_scale_of_same_span (edgeChoice_spec (edgeSpanOfIndex i))
    have ep : chartSpanEval p (edgeSpanOfIndex i) =
        t * graphChow p.val (g i.val.1) (g i.val.2) := by
      unfold chartSpanEval spanChow
      rw [hm, graphIndexChow]
    have eq : chartSpanEval q (edgeSpanOfIndex i) =
        t * graphChow q.val (g i.val.1) (g i.val.2) := by
      unfold chartSpanEval spanChow
      rw [hm, graphIndexChow]
    have hb := congrFun he (edgeSpanOfIndex i)
    change strictBit (chartSpanEval p _) = strictBit (chartSpanEval q _) at hb
    rw [ep,eq] at hb
    exact (strictBit_scale_eq_iff ht (chartChow_ne_zero p i.property)
      (chartChow_ne_zero q i.property)).mp hb
  · intro he
    funext S
    rw [chartSpanBits_eval, chartSpanBits_eval, he]

theorem chartSpanBits_fixed (p q : ChartDomain) :
    chartSpanBits p (edgeSpanOfIndex ⟨(1,5),edge34⟩) =
      chartSpanBits q (edgeSpanOfIndex ⟨(1,5),edge34⟩) := by
  let i : EdgeIndex := ⟨(1,5),edge34⟩
  obtain ⟨t,_,hm⟩ := indexedChow_scale_of_same_span (edgeChoice_spec (edgeSpanOfIndex i))
  have he (x : ChartDomain) : chartSpanEval x (edgeSpanOfIndex i) = t * (1/2) := by
    unfold chartSpanEval spanChow
    rw [hm, graphIndexChow]
    exact congrArg (t * ·) (chow34 _ _ _ _)
  change strictBit (chartSpanEval p (edgeSpanOfIndex i)) =
    strictBit (chartSpanEval q (edgeSpanOfIndex i))
  rw [he,he]

theorem chartSpanBits_no_flip (p q : ChartDomain) :
    chartSpanBits p ≠ flipBits (chartSpanBits q) := by
  intro he
  let i := edgeSpanOfIndex ⟨(1,5),edge34⟩
  have hc := congrFun he i
  change chartSpanBits p i = !(chartSpanBits q i) at hc
  rw [chartSpanBits_fixed p q] at hc
  change chartSpanBits q i = !(chartSpanBits q i) at hc
  cases h : chartSpanBits q i <;> simp [h] at hc

theorem nativeSign_on_chart (p : ChartDomain) :
    nativeSign (nativeChartHomeomorph p) = signClass (chartSpanBits p) := by
  symm
  exact nativeSign_of_basis _ _ _ (graph_basis _ _ _ _) (graph_span _ _ _ _)

theorem nativeSign_on_chart_eq_iff (p q : ChartDomain) :
    nativeSign (nativeChartHomeomorph p) = nativeSign (nativeChartHomeomorph q) ↔
      edgeSign p = edgeSign q := by
  rw [nativeSign_on_chart, nativeSign_on_chart, signClass_eq_iff]
  simp [chartSpanBits_no_flip, chartSpanBits_eq_iff]

end
end G366022
```

## NativeCount.lean

```lean
import NativeSigns
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin

namespace G366022
noncomputable section

abbrev NativeComponents :=
  ↥(Set.range (connectedComponent : NativeDomain → Set NativeDomain))

abbrev NativeRealizedSigns := ↥(Set.range nativeSign)

instance : Finite NativeRealizedSigns := Subtype.finite

def nativeWitness (b : Bool) : NativeDomain := nativeChartHomeomorph (chartWitness b)

instance : Nonempty NativeRealizedSigns :=
  ⟨⟨nativeSign (nativeWitness true), ⟨nativeWitness true,rfl⟩⟩⟩

theorem native_preconnected_sign {S : Set NativeDomain} (hS : IsPreconnected S)
    {u v : NativeDomain} (hu : u ∈ S) (hv : v ∈ S) : nativeSign u = nativeSign v := by
  let e := nativeChartHomeomorph
  have ht := hS.image e.symm e.symm.continuous.continuousOn
  have h := preconnected_chart_sign_const ht
    (Set.mem_image_of_mem e.symm hu) (Set.mem_image_of_mem e.symm hv)
  have hs := (nativeSign_on_chart_eq_iff (e.symm u) (e.symm v)).mpr h
  simpa only [e, Homeomorph.apply_symm_apply] using hs

theorem native_sign_const_on_component {u v : NativeDomain}
    (he : connectedComponent u = connectedComponent v) : nativeSign u = nativeSign v :=
  native_preconnected_sign isConnected_connectedComponent.isPreconnected
    mem_connectedComponent (he ▸ mem_connectedComponent)

theorem native_witness_components_ne :
    connectedComponent (nativeWitness true) ≠ connectedComponent (nativeWitness false) := by
  intro he
  have ht := (isConnected_connectedComponent (x := nativeWitness true)).isPreconnected.image
    nativeChartHomeomorph.symm nativeChartHomeomorph.symm.continuous.continuousOn
  apply no_preconnected_chart_witnesses ht
  · exact ⟨nativeWitness true,mem_connectedComponent,
      nativeChartHomeomorph.symm_apply_apply _⟩
  · exact ⟨nativeWitness false,he ▸ mem_connectedComponent,
      nativeChartHomeomorph.symm_apply_apply _⟩

theorem native_witness_sign_eq :
    nativeSign (nativeWitness true) = nativeSign (nativeWitness false) :=
  (nativeSign_on_chart_eq_iff _ _).mpr witness_sign_equal

def componentPoint (C : NativeComponents) : NativeDomain := C.property.choose

theorem componentPoint_spec (C : NativeComponents) :
    connectedComponent (componentPoint C) = C.val := C.property.choose_spec

def componentSign (C : NativeComponents) : NativeRealizedSigns :=
  ⟨nativeSign (componentPoint C), ⟨componentPoint C,rfl⟩⟩

def componentOf (W : NativeDomain) : NativeComponents :=
  ⟨connectedComponent W, ⟨W,rfl⟩⟩

theorem componentSign_spec (W : NativeDomain) :
    (componentSign (componentOf W)).val = nativeSign W :=
  native_sign_const_on_component (componentPoint_spec (componentOf W))

theorem componentSign_surjective : Function.Surjective componentSign := by
  rintro ⟨s,W,rfl⟩
  exact ⟨componentOf W,Subtype.ext (componentSign_spec W)⟩

theorem componentSign_not_injective : ¬ Function.Injective componentSign := by
  intro he
  apply native_witness_components_ne
  change (componentOf (nativeWitness true)).val = (componentOf (nativeWitness false)).val
  exact congrArg (fun C : NativeComponents => C.val) (he (by
    apply Subtype.ext
    rw [componentSign_spec,componentSign_spec,native_witness_sign_eq]))
theorem native_finite_cell_count_gt [Finite NativeComponents] :
    Nat.card NativeRealizedSigns < Nat.card NativeComponents := by
  let := Fintype.ofFinite NativeComponents
  let := Fintype.ofFinite NativeRealizedSigns
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective componentSign
      componentSign_surjective componentSign_not_injective

theorem native_nat_cell_count_ne :
    Nat.card NativeComponents ≠ Nat.card NativeRealizedSigns := by
  classical
  cases finite_or_infinite NativeComponents with
  | inl h =>
    let := h
    exact ne_of_gt native_finite_cell_count_gt
  | inr h =>
    let := h
    rw [Nat.card_eq_zero_of_infinite]
    exact ne_of_lt Nat.card_pos

theorem native_cell_count_ne :
    ¬ Nonempty (NativeComponents ≃ NativeRealizedSigns) :=
  fun ⟨e⟩ => native_nat_cell_count_ne (Nat.card_congr e)

end
end G366022
```

## NativePolytope.lean

```lean
import NativeCount
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace G366022
noncomputable section

def heightOne : AffineSubspace ℝ R := AffineSubspace.mk' (g 0) h.ker

theorem mem_heightOne (x : R) : x ∈ heightOne ↔ h x = 1 := by
  rw [heightOne, AffineSubspace.mem_mk']
  change h (x - g 0) = 0 ↔ h x = 1
  rw [map_sub,h_g,sub_eq_zero]

theorem affineHull_eq_heightOne : affineSpan ℝ P = heightOne := by
  apply le_antisymm
  · exact affineSpan_le.mpr fun x hx => (mem_heightOne x).mpr (in_chart hx)
  · intro x hx
    let T := affineSpan ℝ P
    have hg (i : Fin 8) : g i ∈ T := subset_affineSpan ℝ P (g_mem i)
    have hd (i : Fin 8) : g i - g 0 ∈ T.direction :=
      AffineSubspace.vsub_mem_direction (hg i) (hg 0)
    have he : x - g 0 = x 2 • (g 1 - g 0) + (2*x 1) • (g 2 - g 0) +
        (2*x 3) • (g 4 - g 0) := by
      have hh := (mem_heightOne x).mp hx
      rw [h_apply] at hh
      funext i
      fin_cases i <;> norm_num [g,gQ] <;> linarith
    have hdir : x - g 0 ∈ T.direction := by
      rw [he]
      exact T.direction.add_mem
        (T.direction.add_mem (T.direction.smul_mem _ (hd 1))
          (T.direction.smul_mem _ (hd 2))) (T.direction.smul_mem _ (hd 4))
    have hm := AffineSubspace.vadd_mem_of_mem_direction hdir (hg 0)
    change x - g 0 + g 0 ∈ T at hm
    exact sub_add_cancel x (g 0) ▸ hm

theorem affineHull_dim : Module.finrank ℝ (affineSpan ℝ P).direction = 3 := by
  have hr : LinearMap.range h = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    exact ⟨a • g 0, by rw [map_smul,h_g,smul_eq_mul,mul_one]⟩
  have hh := h.finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hh
  rw [affineHull_eq_heightOne, heightOne, AffineSubspace.direction_mk']
  have he : 1 + Module.finrank ℝ h.ker = 4 := hh
  exact Nat.add_left_cancel (he.trans (show 4 = 1 + 3 by rfl))

abbrev NonzeroFour := {x : R // x ≠ 0}

def pointSetoid : Setoid NonzeroFour where
  r x y := ∃ t : ℝ, t ≠ 0 ∧ y.val = t • x.val
  iseqv := by
    constructor
    · intro x
      exact ⟨1, one_ne_zero, (one_smul ℝ x.val).symm⟩
    · rintro x y ⟨t,ht,h⟩
      refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
      rw [h, smul_smul, inv_mul_cancel₀ ht, one_smul]
    · rintro x y z ⟨t,ht,h⟩ ⟨s,hs,k⟩
      exact ⟨s*t, mul_ne_zero hs ht, by rw [k,h,smul_smul]⟩

def ProjectivePoint := Quotient pointSetoid

instance : TopologicalSpace ProjectivePoint := by
  unfold ProjectivePoint
  infer_instance

def pointProject (x : NonzeroFour) : ProjectivePoint := Quotient.mk pointSetoid x

theorem pointProject_quotient : Topology.IsQuotientMap pointProject :=
  @isQuotientMap_quotient_mk' _ _ pointSetoid

theorem pointProject_eq_iff (x y : NonzeroFour) :
    pointProject x = pointProject y ↔ ∃ t : ℝ, t ≠ 0 ∧ y.val = t • x.val :=
  ⟨fun e => @Quotient.exact _ pointSetoid _ _ e,
    fun e => @Quotient.sound _ pointSetoid _ _ e⟩

def InHeightPatch (q : ProjectivePoint) : Prop :=
  Quotient.lift (fun x : NonzeroFour => h x.val ≠ 0) (by
    rintro x y ⟨a,ha,e⟩
    apply propext
    rw [e,map_smul,smul_eq_mul]
    exact ⟨mul_ne_zero ha, fun hn hz => hn (by rw [hz,mul_zero])⟩) q

abbrev HeightPatch := {q : ProjectivePoint // InHeightPatch q}

theorem heightPatch_open : IsOpen {q : ProjectivePoint | InHeightPatch q} := by
  apply pointProject_quotient.isCoinducing.isOpen_preimage.mp
  change IsOpen {x : NonzeroFour | h x.val ≠ 0}
  have hc : Continuous (fun x : R => h x) := by
    simp only [h_apply]
    fun_prop
  exact isOpen_ne_fun (hc.comp continuous_subtype_val) continuous_const

def heightNormalize (q : ProjectivePoint) : R :=
  Quotient.lift (fun x : NonzeroFour => (h x.val)⁻¹ • x.val) (by
    rintro x y ⟨a,ha,e⟩
    rw [e,map_smul,smul_eq_mul]
    funext i
    change (h x.val)⁻¹ * x.val i = (a * h x.val)⁻¹ * (a * x.val i)
    simp only [← div_eq_inv_mul]
    rw [mul_div_mul_left _ _ ha]) q

theorem heightNormalize_continuous :
    Continuous (fun q : HeightPatch => heightNormalize q.val) := by
  apply (pointProject_quotient.restrictPreimage_isOpen heightPatch_open).continuous_iff.mpr
  let X := {x : NonzeroFour // x ∈ pointProject ⁻¹' {q | InHeightPatch q}}
  change Continuous (fun x : X => (h x.val.val)⁻¹ • x.val.val)
  have hc : Continuous (fun x : R => h x) := by
    simp only [h_apply]
    fun_prop
  have hv : Continuous (fun x : X => x.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((hc.comp hv).inv₀ (fun x => x.property)).smul hv

theorem heightNormalize_h (q : ProjectivePoint) (hq : InHeightPatch q) :
    h (heightNormalize q) = 1 := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change h ((h x.val)⁻¹ • x.val) = 1
    rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hq]

def heightRep (x : H) : NonzeroFour :=
  ⟨x.val,fun hz => by have hx := x.property; rw [hz,map_zero] at hx; exact zero_ne_one hx⟩

def heightProject (x : H) : HeightPatch :=
  ⟨pointProject (heightRep x),fun hn => one_ne_zero (x.property.symm.trans hn)⟩

def heightHomeomorph : H ≃ₜ HeightPatch where
  toFun := heightProject
  invFun q := ⟨heightNormalize q.val,heightNormalize_h q.val q.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    change (h x.val)⁻¹ • x.val = x.val
    rw [x.property,inv_one,one_smul]
  right_inv := by
    rintro ⟨q,hq⟩
    apply Subtype.ext
    induction q using Quotient.inductionOn with
    | _ x =>
      apply (pointProject_eq_iff _ _).mpr
      change ∃ t : ℝ, t ≠ 0 ∧ x.val = t • ((h x.val)⁻¹ • x.val)
      exact ⟨h x.val,hq,by rw [smul_smul,mul_inv_cancel₀ hq,one_smul]⟩
  continuous_toFun := continuous_induced_rng.2
    (pointProject_quotient.continuous.comp (continuous_induced_rng.2 continuous_subtype_val))
  continuous_invFun := continuous_induced_rng.2 heightNormalize_continuous

def projectivePolytope : Set ProjectivePoint :=
  pointProject '' {x : NonzeroFour | InPositiveCone x.val}

def projectivePlane (W : Submodule ℝ R) : Set ProjectivePoint :=
  pointProject '' {x : NonzeroFour | x.val ∈ W}

theorem projectiveStabs_iff (W : Submodule ℝ R) :
    NativeStabs W ↔ (projectivePolytope ∩ projectivePlane W).Nonempty := by
  constructor
  · rintro ⟨x,hx,hw⟩
    exact ⟨pointProject ⟨x,hx.1⟩,⟨⟨⟨x,hx.1⟩,hx,rfl⟩,⟨⟨x,hx.1⟩,hw,rfl⟩⟩⟩
  · rintro ⟨q,⟨x,hx,hq⟩,y,hy,hyq⟩
    obtain ⟨t,ht,he⟩ := (pointProject_eq_iff x y).mp (hq.trans hyq.symm)
    refine ⟨x.val,hx,?_⟩
    have hmem := W.smul_mem t⁻¹ hy
    rwa [he,smul_smul,inv_mul_cancel₀ ht,one_smul] at hmem

theorem projectivePolytope_image :
    projectivePolytope = (fun x : H => (heightHomeomorph x).val) '' PChart := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    let y : HeightPatch := ⟨pointProject x,ne_of_gt (cone_h_pos hx)⟩
    refine ⟨heightHomeomorph.symm y,cone_normalized_mem hx,?_⟩
    exact congrArg Subtype.val (heightHomeomorph.apply_symm_apply y)
  · rintro ⟨x,hx,rfl⟩
    exact ⟨heightRep x,chart_point_in_cone hx,rfl⟩

theorem projective_polytope_interior :
    (interior (heightHomeomorph '' PChart)).Nonempty := by
  rw [← heightHomeomorph.image_interior]
  exact chart_interior_nonempty.image _

theorem native_witness_interior (b : Bool) :
    heightHomeomorph (witness b) ∈ interior (heightHomeomorph '' PChart) ∧
    (heightHomeomorph (witness b)).val ∈ projectivePlane (nativeWitness b).val.val := by
  constructor
  · rw [← heightHomeomorph.image_interior]
    exact ⟨witness b,witness_interior b,rfl⟩
  · exact ⟨heightRep (witness b),witness_graph b,rfl⟩

end
end G366022
```

## LiteralEndpoint.lean

```lean
import NativePolytope

namespace G366022
noncomputable section

def pluckerHomeomorph : RealGr ≃ₜ {p : ProjectiveSix // Decomposable p} := by
  let f (W : RealGr) : {p : ProjectiveSix // Decomposable p} :=
    ⟨plucker W, by
      change plucker W ∈ {p | Decomposable p}
      rw [← plucker_range]
      exact ⟨W,rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro U V he
      exact plucker_injective (congrArg Subtype.val he)
    · intro q
      have hq : q.val ∈ Set.range plucker := plucker_range.symm ▸ q.property
      obtain ⟨W,hW⟩ := hq
      exact ⟨W,Subtype.ext hW⟩
  let e := Equiv.ofBijective f hbij
  apply e.toHomeomorphOfIsInducing
  constructor
  change realGrTopology = TopologicalSpace.induced e (TopologicalSpace.induced Subtype.val _)
  rw [induced_compose]
  rfl

theorem projectivePlane_inter_iff (U V : Submodule ℝ R) :
    (projectivePlane U ∩ projectivePlane V).Nonempty ↔ ¬ Disjoint U V := by
  rw [Submodule.disjoint_def]
  constructor
  · rintro ⟨q,⟨x,hx,hq⟩,y,hy,hyq⟩ hd
    obtain ⟨t,ht,he⟩ := (pointProject_eq_iff x y).mp (hq.trans hyq.symm)
    have hv : x.val ∈ V := by
      have hmem := V.smul_mem t⁻¹ hy
      rwa [he,smul_smul,inv_mul_cancel₀ ht,one_smul] at hmem
    exact x.property (hd x.val hx hv)
  · intro hd
    push Not at hd
    obtain ⟨x,hx,hy,hn⟩ := hd
    exact ⟨pointProject ⟨x,hn⟩,⟨⟨⟨x,hn⟩,hx,rfl⟩,⟨⟨x,hn⟩,hy,rfl⟩⟩⟩

def stabbingSet : Set RealGr :=
  {W | (projectivePolytope ∩ projectivePlane W.val).Nonempty}

def faceDivisors : Set RealGr :=
  {W | ∃ S : NativeEdgeSpan, (projectivePlane W.val ∩ projectivePlane S.val).Nonempty}

def stabbingComplement : Set RealGr := stabbingSet \ faceDivisors

theorem literal_complement_eq :
    stabbingComplement = {W : RealGr | NativeStabs W.val ∧ NativeAway W.val} := by
  classical
  ext W
  change ((projectivePolytope ∩ projectivePlane W.val).Nonempty ∧
    ¬ ∃ S : NativeEdgeSpan, (projectivePlane W.val ∩ projectivePlane S.val).Nonempty) ↔
      NativeStabs W.val ∧ NativeAway W.val
  rw [← projectiveStabs_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hn F hF
    by_contra hd
    exact hn ⟨⟨Submodule.span ℝ F,⟨F,hF,rfl⟩⟩,(projectivePlane_inter_iff _ _).mpr hd⟩
  · rintro ha ⟨S,hS⟩
    obtain ⟨F,hF,hs⟩ := S.property
    exact (projectivePlane_inter_iff _ _).mp hS (hs ▸ ha F hF)

def grassmannianChowSign (W : RealGr) : ProjectiveSigns :=
  signClass (strictBit ∘ spanChow (frame W).1 (frame W).2)

theorem literal_cell_count_ne :
    Nat.card ↥(Set.range (fun W : stabbingComplement => connectedComponent W)) ≠
      Nat.card ↥(Set.range (fun W : stabbingComplement => grassmannianChowSign W.val)) := by
  rw [literal_complement_eq]
  exact native_nat_cell_count_ne

theorem literal_no_bijection :
    ¬ Nonempty
      (↥(Set.range (fun W : stabbingComplement => connectedComponent W)) ≃
        ↥(Set.range (fun W : stabbingComplement => grassmannianChowSign W.val))) := by
  rintro ⟨e⟩
  exact literal_cell_count_ne (Nat.card_congr e)

theorem mathdb_366022_counterexample :
    Module.finrank ℝ (affineSpan ℝ P).direction = 3 ∧
    (interior (heightHomeomorph '' PChart)).Nonempty ∧
    ¬ Nonempty
      (↥(Set.range (fun W : ↥(stabbingSet \ faceDivisors) => connectedComponent W)) ≃
        ↥(Set.range (fun W : ↥(stabbingSet \ faceDivisors) => grassmannianChowSign W.val))) :=
  ⟨affineHull_dim, projective_polytope_interior, literal_no_bijection⟩

end
end G366022
```

## NativeAudit.lean

```lean
import LiteralEndpoint

namespace G366022


#check (mathdb_366022_counterexample :
  Module.finrank ℝ (affineSpan ℝ P).direction = 3 ∧
  (interior (heightHomeomorph '' PChart)).Nonempty ∧
  ¬ Nonempty
    (↥(Set.range (fun W : ↥(stabbingSet \ faceDivisors) => connectedComponent W)) ≃
      ↥(Set.range (fun W : ↥(stabbingSet \ faceDivisors) => grassmannianChowSign W.val))))
#check (literal_cell_count_ne :
  Nat.card ↥(Set.range (fun W : stabbingComplement => connectedComponent W)) ≠
    Nat.card ↥(Set.range (fun W : stabbingComplement => grassmannianChowSign W.val)))
#print realGrTopology
#print NativeStabs
#print NativeAway
#print NativeDomain
#print stabbingSet
#print faceDivisors
#print stabbingComplement
#print grassmannianChowSign
#print NativeComponents
#print NativeRealizedSigns
#check nativeChart_agrees
#check native_witness_interior
#check componentSign_surjective
#check componentSign_not_injective

#print axioms minor
#print axioms minors
#print axioms minor_expand
#print axioms minors_expand
#print axioms minor_scale_of_minors
#print axioms exists_minor_ne
#print axioms minors_ne_zero
#print axioms spanPair_eq_of_minor_scale
#print axioms minors_scale_of_spanPair_eq
#print axioms Six
#print axioms NonzeroSix
#print axioms scalarSetoid
#print axioms ProjectiveSix
#print axioms project
#print axioms project_quotient
#print axioms project_eq_iff
#print axioms projectMinor
#print axioms RealGr
#print axioms frame
#print axioms frame_spec
#print axioms plucker
#print axioms plucker_of_span
#print axioms plucker_injective
#print axioms spanPair_rank
#print axioms independent_of_minors_ne
#print axioms Decomposable
#print axioms plucker_range
#print axioms plucker_embedding
#print axioms InFirstPatch
#print axioms firstPatch_open
#print axioms FirstPatch
#print axioms NormalizedSix
#print axioms projectRatios
#print axioms projectRatios_continuous
#print axioms projectRatios_first
#print axioms normalizedProject
#print axioms firstPatchHomeomorph
#print axioms NativeStabs
#print axioms NativeAway
#print axioms NativeDomain
#print axioms nativePlaneEquiv
#print axioms chartNativeEquiv
#print axioms nativePatch
#print axioms nativePatch_continuous
#print axioms graphMinors
#print axioms graphMinors_eq
#print axioms graphMinors_continuous
#print axioms normalizedGraph
#print axioms normalizedGraph_continuous
#print axioms chartNative_plucker
#print axioms nativePatch_on_chart
#print axioms extractGraph
#print axioms extractGraph_continuous
#print axioms extractGraph_normalized
#print axioms chartNative_continuous
#print axioms nativeChart_continuous
#print axioms nativeChartHomeomorph
#print axioms nativeChart_agrees
#print axioms primalMinors
#print axioms sourceChow
#print axioms sourceChow_det
#print axioms sourceChow_plane_scale
#print axioms sourceChow_edge_scale
#print axioms NativeEdgeSpan
#print axioms edgeSpanOfIndex
#print axioms edgeSpanOfIndex_surjective
#print axioms edgeChoice
#print axioms edgeChoice_spec
#print axioms indexedChow
#print axioms indexedChow_scale_of_same_span
#print axioms spanChow
#print axioms spanChow_basis_scale
#print axioms strictBit
#print axioms strictBit_mul_pos
#print axioms strictBit_mul_neg
#print axioms strictBit_scale_eq_iff
#print axioms SpanBits
#print axioms flipBits
#print axioms flipBits_involutive
#print axioms signSetoid
#print axioms ProjectiveSigns
#print axioms signClass
#print axioms signClass_eq_iff
#print axioms class_scale
#print axioms nativeEval
#print axioms nativeEval_ne_zero
#print axioms nativeSign
#print axioms nativeSign_of_basis
#print axioms chartSpanEval
#print axioms graphIndexChow
#print axioms chartSpanEval_eq
#print axioms chartSpanEval_ne_zero
#print axioms chartSpanBits
#print axioms chartSpanBits_eval
#print axioms chartSpanBits_eq_iff
#print axioms chartSpanBits_fixed
#print axioms chartSpanBits_no_flip
#print axioms nativeSign_on_chart
#print axioms nativeSign_on_chart_eq_iff
#print axioms NativeComponents
#print axioms NativeRealizedSigns
#print axioms nativeWitness
#print axioms native_preconnected_sign
#print axioms native_sign_const_on_component
#print axioms native_witness_components_ne
#print axioms native_witness_sign_eq
#print axioms componentPoint
#print axioms componentPoint_spec
#print axioms componentSign
#print axioms componentOf
#print axioms componentSign_spec
#print axioms componentSign_surjective
#print axioms componentSign_not_injective
#print axioms native_finite_cell_count_gt
#print axioms native_nat_cell_count_ne
#print axioms native_cell_count_ne
#print axioms heightOne
#print axioms mem_heightOne
#print axioms affineHull_eq_heightOne
#print axioms affineHull_dim
#print axioms NonzeroFour
#print axioms pointSetoid
#print axioms ProjectivePoint
#print axioms pointProject
#print axioms pointProject_quotient
#print axioms pointProject_eq_iff
#print axioms InHeightPatch
#print axioms HeightPatch
#print axioms heightPatch_open
#print axioms heightNormalize
#print axioms heightNormalize_continuous
#print axioms heightNormalize_h
#print axioms heightRep
#print axioms heightProject
#print axioms heightHomeomorph
#print axioms projectivePolytope
#print axioms projectivePlane
#print axioms projectiveStabs_iff
#print axioms projectivePolytope_image
#print axioms projective_polytope_interior
#print axioms native_witness_interior
#print axioms pluckerHomeomorph
#print axioms projectivePlane_inter_iff
#print axioms stabbingSet
#print axioms faceDivisors
#print axioms stabbingComplement
#print axioms literal_complement_eq
#print axioms grassmannianChowSign
#print axioms literal_cell_count_ne
#print axioms literal_no_bijection
#print axioms mathdb_366022_counterexample
#print axioms realGrTopology
#print axioms stabs_iff_nonzero_cone
#print axioms away_native_iff
#print axioms native_edge_span_iff
#print axioms chart_witnesses_components_ne
#print axioms preconnected_chart_sign_const
#print axioms chart_interior_nonempty
#print axioms all_edge_product_pos
#print axioms witness_sign_equal

end G366022
```


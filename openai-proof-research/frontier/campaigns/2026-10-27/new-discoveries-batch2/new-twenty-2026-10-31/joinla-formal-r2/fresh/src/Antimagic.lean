import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Int.Sum

namespace R159
open Finset
abbrev E := Fin 6 × Fin 5
abbrev V := (Fin 6 × Bool) ⊕ (Fin 2 × Bool)

-- Six matching edges, three per component; four join edges at each matched pair.
def ends (e : E) : V × V :=
  match e.2.val with
  | 0 => (.inl (e.1, false), .inl (e.1, true))
  | 1 => (.inl (e.1, false), .inr (⟨e.1.val / 3, by omega⟩, false))
  | 2 => (.inl (e.1, false), .inr (⟨e.1.val / 3, by omega⟩, true))
  | 3 => (.inl (e.1, true), .inr (⟨e.1.val / 3, by omega⟩, false))
  | _ => (.inl (e.1, true), .inr (⟨e.1.val / 3, by omega⟩, true))

def wt (f : E → ℤ) (v : V) : ℤ :=
  ∑ e : E, if (ends e).1 = v ∨ (ends e).2 = v then f e else 0

def L (f : E → ℤ) (t : Fin 6) := f (t,0) + f (t,1) + f (t,2)
def R (f : E → ℤ) (t : Fin 6) := f (t,0) + f (t,3) + f (t,4)
def O (f : E → ℤ) (h : Fin 2) (b : Bool) :=
  ∑ j : Fin 3, (if b then f (⟨3*h.val+j.val, by omega⟩,2) +
    f (⟨3*h.val+j.val, by omega⟩,4)
    else f (⟨3*h.val+j.val, by omega⟩,1) + f (⟨3*h.val+j.val, by omega⟩,3))

lemma wt_left (f : E → ℤ) (t : Fin 6) :
    wt f (.inl (t,false)) = L f t := by
  fin_cases t <;> simp [wt, ends, L, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring
lemma wt_right (f : E → ℤ) (t : Fin 6) :
    wt f (.inl (t,true)) = R f t := by
  fin_cases t <;> simp [wt, ends, R, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring
lemma wt_null (f : E → ℤ) (h : Fin 2) (b : Bool) :
    wt f (.inr (h,b)) = O f h b := by
  fin_cases h <;> cases b <;>
    simp [wt, ends, O, Fintype.sum_prod_type, Fin.sum_univ_succ]

def Labeling (f : E → ℤ) : Prop :=
  Function.Injective f ∧ (∀ e, 1 ≤ f e ∧ f e ≤ 30)
def Proper (f : E → ℤ) : Prop :=
  ∀ e, wt f (ends e).1 ≠ wt f (ends e).2

lemma total (f : E → ℤ) (hf : Labeling f) : ∑ e, f e = 465 := by
  have hi : (univ.image f) = Icc (1:ℤ) 30 := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, _, rfl⟩ := mem_image.mp hx
      exact mem_Icc.mpr (hf.2 e)
    · rw [card_image_of_injective _ hf.1]
      norm_num
  have hh := sum_image (s := (univ : Finset E)) (f := id) (g := f)
    (fun a _ b _ h => hf.1 h)
  rw [hi] at hh
  norm_num at hh
  exact hh.symm

lemma palette {a b c x y z w : ℤ}
    (hx : x=a ∨ x=b ∨ x=c) (hy : y=a ∨ y=b ∨ y=c)
    (hz : z=a ∨ z=b ∨ z=c) (hw : w=a ∨ w=b ∨ w=c)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    w=x ∨ w=y ∨ w=z := by omega

lemma pair_sum {a b c x y z : ℤ}
    (hx : x=a ∨ x=b ∨ x=c) (hy : y=a ∨ y=b ∨ y=c)
    (hz : z=a ∨ z=b ∨ z=c)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    x+y+z=a+b+c := by omega

lemma twelve_lower (f : E → ℤ) (hf : Labeling f)
    (s : Finset E) (hc : s.card = 12) : 78 ≤ ∑ e ∈ s, f e := by
  have hh := Finset.sum_range_le_sum (s := s.image f) (c := (1:ℤ))
    (by intro x hx; obtain ⟨e, _, rfl⟩ := mem_image.mp hx; exact (hf.2 e).1)
  rw [card_image_of_injective _ hf.1, hc] at hh
  rw [sum_image (fun a _ b _ h => hf.1 h)] at hh
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ] at hh
  exact hh

#print axioms wt_left
#print axioms total
end R159

namespace R159
open Finset
def M (f : E → ℤ) : ℤ := ∑ t : Fin 6, f (t,0)
def Mc (f : E → ℤ) (h : Fin 2) : ℤ :=
 ∑ j : Fin 3, f (⟨3*h.val+j.val, by omega⟩,0)
def pc (f : E → ℤ) (h : Fin 2) : ℤ :=
 ∑ j : Fin 3, (L f ⟨3*h.val+j.val, by omega⟩ + R f ⟨3*h.val+j.val, by omega⟩)

lemma component_count (f : E → ℤ) (h : Fin 2) :
  pc f h = 2*Mc f h + O f h false + O f h true := by
 fin_cases h <;> simp [pc, Mc, O, L, R, Fin.sum_univ_succ] <;> ring
lemma all_count (f : E → ℤ) :
  (∑ e, f e) = M f + O f 0 false + O f 0 true + O f 1 false + O f 1 true := by
 simp [M, O, Fintype.sum_prod_type, Fin.sum_univ_succ]
 ring
lemma m_count (f : E → ℤ) : M f = Mc f 0 + Mc f 1 := by
 simp [M, Mc, Fin.sum_univ_succ]
 ring
lemma m_upper (f : E → ℤ) (hf : Labeling f) : M f ≤ 180 := by
 have hh := sum_le_sum (s := (univ : Finset (Fin 6)))
    (f := fun t => f (t,0)) (g := fun _ => (30:ℤ))
    (fun t _ => (hf.2 (t,0)).2)
 simpa [M] using hh

lemma triangle_proper (f : E → ℤ) (hp : Proper f) (t : Fin 6) (b : Bool) :
 L f t ≠ R f t ∧ L f t ≠ O f ⟨t.val/3, by omega⟩ b ∧
 R f t ≠ O f ⟨t.val/3, by omega⟩ b := by
 have h0 := hp (t,0)
 have h1 := hp (t,1)
 have h2 := hp (t,2)
 have h3 := hp (t,3)
 have h4 := hp (t,4)
 simp [ends, wt_left, wt_right, wt_null] at h0 h1 h2 h3 h4
 cases b
 · exact ⟨h0,h1,h3⟩
 · exact ⟨h0,h2,h4⟩

def Three (f : E → ℤ) : Prop :=
 ∃ a b c : ℤ, ∀ v, wt f v = a ∨ wt f v = b ∨ wt f v = c

lemma canonical_palette (f : E → ℤ) (hp : Proper f) (ht : Three f) :
 ∀ v, wt f v = L f 0 ∨ wt f v = R f 0 ∨ wt f v = O f 0 false := by
 obtain ⟨a,b,c,h⟩ := ht
 intro v
 have h0 := h (.inl (0,false))
 have h1 := h (.inl (0,true))
 have h2 := h (.inr (0,false))
 rw [wt_left] at h0
 rw [wt_right] at h1
 rw [wt_null] at h2
 have p := triangle_proper f hp 0 false
 exact palette h0 h1 h2 (h v) p.1 p.2.1 p.2.2

lemma null_same (f : E → ℤ) (hp : Proper f) (ht : Three f) (h : Fin 2) :
 O f h false = O f h true := by
 obtain ⟨a,b,c,hh⟩ := ht
 let t : Fin 6 := ⟨3*h.val, by omega⟩
 have h0 := hh (.inl (t,false))
 have h1 := hh (.inl (t,true))
 have h2 := hh (.inr (h,false))
 have h3 := hh (.inr (h,true))
 rw [wt_left] at h0
 rw [wt_right] at h1
 rw [wt_null] at h2 h3
 have p := triangle_proper f hp t false
 have q := triangle_proper f hp t true
 have he : (⟨t.val/3, by omega⟩ : Fin 2) = h := by apply Fin.ext; dsimp [t]; omega
 rw [he] at p q
 have := palette h0 h1 h2 h3 p.1 p.2.1 p.2.2
 omega

lemma pair_total (f : E → ℤ) (hp : Proper f) (ht : Three f) (t : Fin 6) :
 L f t + R f t + O f ⟨t.val/3, by omega⟩ false =
 L f 0 + R f 0 + O f 0 false := by
 have h := canonical_palette f hp ht
 have h0 := h (.inl (t,false))
 have h1 := h (.inl (t,true))
 have h2 := h (.inr (⟨t.val/3, by omega⟩,false))
 rw [wt_left] at h0
 rw [wt_right] at h1
 rw [wt_null] at h2
 have p := triangle_proper f hp 0 false
 have q := triangle_proper f hp t false
 exact pair_sum h0 h1 h2 p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2

end R159

namespace R159
open Finset
def J (b : Fin 6 → Bool) (x : Fin 6 × Fin 2) : E :=
 (x.1, if b x.1 then (if x.2 = 0 then 3 else 4) else (if x.2 = 0 then 1 else 2))
def Qs (b : Fin 6 → Bool) : Finset E := univ.image (J b)
lemma j_inj (b : Fin 6 → Bool) : Function.Injective (J b) := by
 intro ⟨t,i⟩ ⟨u,j⟩ h
 have he : t=u := congrArg Prod.fst h
 subst u
 have h2 := congrArg Prod.snd h
 fin_cases i <;> fin_cases j <;> cases hb : b t <;> simp [J,hb] at h2 ⊢
lemma qcard (b : Fin 6 → Bool) : (Qs b).card = 12 := by
 rw [Qs, card_image_of_injective _ (j_inj b)]
 norm_num
lemma qidentity (f : E → ℤ) (b : Fin 6 → Bool) (z : ℤ)
 (hw : ∀ t, (if b t then R f t else L f t) = z) :
 6*z = M f + ∑ e ∈ Qs b, f e := by
 have hsel : ∀ t, f (t,0) + f (J b (t,0)) + f (J b (t,1)) = z := by
  intro t
  have hh := hw t
  cases hb : b t <;> simpa [hb,L,R,J] using hh
 have hh := congrArg (fun g : Fin 6 → ℤ => ∑ t, g t) (funext hsel)
 simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
 rw [Qs, sum_image (fun a _ c _ h => j_inj b h), Fintype.sum_prod_type]
 simp only [Fin.sum_univ_two]
 dsimp [M]
 rw [← sum_add_distrib]
 simpa [add_assoc] using hh.symm

lemma pc_total (f : E → ℤ) (hp : Proper f) (ht : Three f) (h : Fin 2) :
 pc f h + 3 * O f h false = 3 * (L f 0 + R f 0 + O f 0 false) := by
 have p0 := pair_total f hp ht 0
 have p1 := pair_total f hp ht 1
 have p2 := pair_total f hp ht 2
 have p3 := pair_total f hp ht 3
 have p4 := pair_total f hp ht 4
 have p5 := pair_total f hp ht 5
 norm_num at p0 p1 p2 p3 p4 p5
 fin_cases h <;> simp [pc, Fin.sum_univ_succ] <;> omega

lemma common_choice (f : E → ℤ) (hp : Proper f) (ht : Three f) (z : ℤ)
 (hz : z=L f 0 ∨ z=R f 0 ∨ z=O f 0 false)
 (hn : ∀ t : Fin 6, O f ⟨t.val/3, by omega⟩ false ≠ z) :
 ∃ b : Fin 6 → Bool, ∀ t, (if b t then R f t else L f t) = z := by
 classical
 have h := canonical_palette f hp ht
 have hh : ∀ t : Fin 6, ∃ b : Bool, (if b then R f t else L f t) = z := by
  intro t
  have hx := h (.inl (t,false))
  have hy := h (.inl (t,true))
  have hnz := h (.inr (⟨t.val/3, by omega⟩,false))
  rw [wt_left] at hx
  rw [wt_right] at hy
  rw [wt_null] at hnz
  have p := triangle_proper f hp t false
  have notz := hn t
  have he : L f t=z ∨ R f t=z := by omega
  rcases he with he|he
  · exact ⟨false,he⟩
  · exact ⟨true,he⟩
 exact ⟨fun t => (hh t).choose, fun t => (hh t).choose_spec⟩

set_option maxHeartbeats 800000 in
theorem no_three (f : E → ℤ) (hf : Labeling f) (hp : Proper f) : ¬ Three f := by
 intro ht
 have sumall := total f hf
 have ns0 := null_same f hp ht 0
 have ns1 := null_same f hp ht 1
 have c0 := component_count f 0
 have c1 := component_count f 1
 have ac := all_count f
 have mc := m_count f
 have p0 := pc_total f hp ht 0
 have p1 := pc_total f hp ht 1
 have tri := triangle_proper f hp 0 false
 norm_num at tri
 have hn := canonical_palette f hp ht (.inr (1,false))
 rw [wt_null] at hn
 by_cases he : O f 1 false = O f 0 false
 · omega
 · have hz : ∃ z, (z=L f 0 ∨ z=R f 0 ∨ z=O f 0 false) ∧
      (∀ t : Fin 6, O f ⟨t.val/3, by omega⟩ false ≠ z) ∧
      L f 0+R f 0+O f 0 false = O f 0 false+O f 1 false+z := by
    rcases hn with hn|hn|hn
    · refine ⟨R f 0, Or.inr (Or.inl rfl), ?_, ?_⟩
      · intro t; fin_cases t <;> norm_num <;> first | exact Ne.symm tri.2.2 | simpa [hn] using tri.1
      · omega
    · refine ⟨L f 0, Or.inl rfl, ?_, ?_⟩
      · intro t; fin_cases t <;> norm_num <;> first | exact Ne.symm tri.2.1 | simpa [hn] using (Ne.symm tri.1)
      · omega
    · exact False.elim (he hn)
   obtain ⟨z,hz,hnz,heq⟩ := hz
   obtain ⟨b,hb⟩ := common_choice f hp ht z hz hnz
   have qi := qidentity f b z hb
   have ql := twelve_lower f hf (Qs b) (qcard b)
   have mu := m_upper f hf
   omega

#print axioms no_three
end R159

namespace R159
-- Direct adjacency of the disjoint union of two joins 3P₂ ∨ O₂.
def sourceAdj : V → V → Prop
 | .inl (t,b), .inl (u,c) => t=u ∧ b≠c
 | .inl (t,_), .inr (h,_) => t.val/3=h.val
 | .inr (h,_), .inl (t,_) => t.val/3=h.val
 | .inr _, .inr _ => False

instance (v w : V) : Decidable (sourceAdj v w) := by
 cases v with
 | inl x => cases w <;> simp only [sourceAdj] <;> infer_instance
 | inr x => cases w <;> simp only [sourceAdj] <;> infer_instance

theorem vertex_count : Fintype.card V = 16 := by decide
theorem edge_count : Fintype.card E = 30 := by decide
theorem source_loopless : ∀ v, ¬sourceAdj v v := by decide
theorem source_symmetric : ∀ v w, sourceAdj v w ↔ sourceAdj w v := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem edge_complete : ∀ v w, sourceAdj v w ↔
 ∃ e, ((ends e).1=v ∧ (ends e).2=w) ∨ ((ends e).1=w ∧ (ends e).2=v) := by
 decide

set_option maxRecDepth 10000 in
theorem edge_unique : ∀ e d, ((ends e).1=(ends d).1 ∧ (ends e).2=(ends d).2) ∨
 ((ends e).1=(ends d).2 ∧ (ends e).2=(ends d).1) → e=d := by decide

-- Labeling is an equivalent, finite formulation of bijection onto {1,...,30}.
theorem labels_bijective (f : E → ℤ) (hf : Labeling f) :
 Function.Injective f ∧ ∀ x : ℤ, (∃ e, f e=x) ↔ 1≤x ∧ x≤30 := by
 refine ⟨hf.1, ?_⟩
 have hi : (Finset.univ.image f) = Finset.Icc (1:ℤ) 30 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (hf.2 e)
  · rw [Finset.card_image_of_injective _ hf.1]; norm_num
 intro x
 have hh := congrArg (fun s : Finset ℤ => x ∈ s) hi
 simpa using hh

theorem source_conjecture_4_1_counterexample :
 ¬ ∃ f : E → ℤ, Labeling f ∧ Proper f ∧
   ∃ a b c : ℤ, ∀ v : V, wt f v=a ∨ wt f v=b ∨ wt f v=c := by
 rintro ⟨f,hf,hp,ht⟩
 exact no_three f hf hp ht

#print axioms source_conjecture_4_1_counterexample
#print axioms edge_complete
#print axioms edge_unique
end R159

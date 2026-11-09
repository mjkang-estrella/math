import Literal
import IntegerCore
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TripleCertificates
open FullereneGeometry
def rv (a : V) : E := ![(a.x:ℝ), (a.y:ℝ), (a.z:ℝ)]
def rp (p : Point) : E := fun k => rv p.num k / (p.den:ℝ)
def rd (a b c : E) : ℝ := a 0*(b 1*c 2-b 2*c 1)-a 1*(b 0*c 2-b 2*c 0)+a 2*(b 0*c 1-b 1*c 0)
theorem dot_rv (a b : V) : dot (rv a) (rv b) = (dp a b : ℤ) := by
 simp [dot, rv, dp, Fin.sum_univ_succ, Int.cast_add, Int.cast_mul, add_assoc]
theorem det_rv (a b c : V) : rd (rv a) (rv b) (rv c) = (det a b c : ℤ) := by
 simp [rd, rv, det, Int.cast_add, Int.cast_mul, Int.cast_sub]
theorem dot_rp (a : V) (p : Point) : dot (rv a) (rp p) = (dp a p.num : ℤ) / (p.den:ℝ) := by
 rw [← dot_rv]
 simp only [dot, rp, div_eq_mul_inv]
 rw [Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro i _
 ring
theorem unique_real (a b c x z : E) (hn : rd a b c ≠ 0)
 (ha : dot a x = dot a z) (hb : dot b x = dot b z) (hc : dot c x = dot c z) : x = z := by
 have h0 : rd a b c * (x 0-z 0) = 0 := by
  simp [dot, Fin.sum_univ_succ] at ha hb hc
  dsimp [rd]
  linear_combination (b 1*c 2-b 2*c 1)*ha + (c 1*a 2-c 2*a 1)*hb + (a 1*b 2-a 2*b 1)*hc
 have h1 : rd a b c * (x 1-z 1) = 0 := by
  simp [dot, Fin.sum_univ_succ] at ha hb hc
  dsimp [rd]
  linear_combination (b 2*c 0-b 0*c 2)*ha + (c 2*a 0-c 0*a 2)*hb + (a 2*b 0-a 0*b 2)*hc
 have h2 : rd a b c * (x 2-z 2) = 0 := by
  simp [dot, Fin.sum_univ_succ] at ha hb hc
  dsimp [rd]
  linear_combination (b 0*c 1-b 1*c 0)*ha + (c 0*a 1-c 1*a 0)*hb + (a 0*b 1-a 1*b 0)*hc
 ext k
 fin_cases k
 · exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hn)
 · exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hn)
 · exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hn)
theorem active_real (a : V) (D : ℤ) (p : Point) (hd : 0 < p.den)
 (ha : active a D p) : dot (rv a) (rp p) = (D:ℝ) := by
 rw [dot_rp, show dp a p.num = D*p.den from ha]
 push_cast
 exact mul_div_cancel_right₀ _ (by exact_mod_cast ne_of_gt hd)
theorem core_unique (a b c : V) (D : ℤ) (p : Point) (h : core a b c D p)
 (x : E) (ha : dot (rv a) x = (D:ℝ)) (hb : dot (rv b) x = (D:ℝ))
 (hc : dot (rv c) x = (D:ℝ)) : x = rp p := by
 apply unique_real (rv a) (rv b) (rv c) x (rp p)
 · rw [det_rv]; exact_mod_cast h.2.1
 · exact ha.trans (active_real a D p h.1 h.2.2.1).symm
 · exact hb.trans (active_real b D p h.1 h.2.2.2.1).symm
 · exact hc.trans (active_real c D p h.1 h.2.2.2.2).symm
theorem bad_real (a b c t : V) (D : ℤ) (p : Point) (h : bad a b c t D p)
 (x : E) (ha : dot (rv a) x = (D:ℝ)) (hb : dot (rv b) x = (D:ℝ))
 (hc : dot (rv c) x = (D:ℝ)) : (D:ℝ) < dot (rv t) x := by
 rw [core_unique a b c D p h.1 x ha hb hc, dot_rp]
 apply (lt_div_iff₀ (by exact_mod_cast h.1.1)).mpr
 exact_mod_cast h.2
theorem same_real (p r : Point) (hp : 0 < p.den) (hr : 0 < r.den) (h : same p r) : rp p = rp r := by
 ext k
 apply (div_eq_div_iff (by exact_mod_cast ne_of_gt hp) (by exact_mod_cast ne_of_gt hr)).mpr
 fin_cases k
 · change (p.num.x:ℝ)*r.den = (r.num.x:ℝ)*p.den; exact_mod_cast h.1
 · change (p.num.y:ℝ)*r.den = (r.num.y:ℝ)*p.den; exact_mod_cast h.2.1
 · change (p.num.z:ℝ)*r.den = (r.num.z:ℝ)*p.den; exact_mod_cast h.2.2
theorem good_real (a b c : V) (D : ℤ) (p r : Point) (h : good a b c D p r)
 (x : E) (ha : dot (rv a) x = (D:ℝ)) (hb : dot (rv b) x = (D:ℝ))
 (hc : dot (rv c) x = (D:ℝ)) : x = rp r :=
 (core_unique a b c D p h.1 x ha hb hc).trans (same_real p r h.1.1 h.2.1 h.2.2)
theorem checked_real (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point)
 (r : Certificate) (h : checked A D P r) (x : E)
 (hf : ∀ t, dot (rv (A t)) x ≤ (D:ℝ))
 (ha : dot (rv (A r.i)) x = (D:ℝ)) (hb : dot (rv (A r.j)) x = (D:ℝ))
 (hc : dot (rv (A r.k)) x = (D:ℝ)) : x ∈ Set.range (fun v => rp (P v)) := by
 unfold checked at h
 split at h
 · exact ⟨r.vertex, (good_real _ _ _ _ _ _ h x ha hb hc).symm⟩
 · exact False.elim ((not_lt_of_ge (hf r.violated)) (bad_real _ _ _ _ _ _ h x ha hb hc))
def triples : List (Fin 32 × Fin 32 × Fin 32) :=
 (List.finRange 32).flatMap fun i => (List.finRange 32).flatMap fun j =>
  ((List.finRange 32).filter fun k => i < j ∧ j < k).map fun k => (i,j,k)
theorem mem_triples (i j k : Fin 32) (hij : i < j) (hjk : j < k) : (i,j,k) ∈ triples := by
 apply List.mem_flatMap.mpr
 refine ⟨i, by simp, ?_⟩
 apply List.mem_flatMap.mpr
 refine ⟨j, by simp, ?_⟩
 apply List.mem_map.mpr
 exact ⟨k, by simp [hij,hjk], rfl⟩
theorem covered_real (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point)
 (rs : List Certificate) (hcheck : ∀ r ∈ rs, checked A D P r)
 (hcover : rs.map Certificate.ids = triples) (i j k : Fin 32) (hij : i<j) (hjk : j<k)
 (x : E) (hf : ∀ t, dot (rv (A t)) x ≤ (D:ℝ))
 (ha : dot (rv (A i)) x = (D:ℝ)) (hb : dot (rv (A j)) x = (D:ℝ))
 (hc : dot (rv (A k)) x = (D:ℝ)) : x ∈ Set.range (fun v => rp (P v)) := by
 have hm := mem_triples i j k hij hjk
 rw [← hcover, List.mem_map] at hm
 obtain ⟨r,hr,he⟩ := hm
 have hi : r.i = i := congrArg Prod.fst he
 have hj : r.j = j := congrArg (fun a => a.2.1) he
 have hk : r.k = k := congrArg (fun a => a.2.2) he
 apply checked_real A D P r (hcheck r hr) x hf
 · simpa [hi] using ha
 · simpa [hj] using hb
 · simpa [hk] using hc
end TripleCertificates

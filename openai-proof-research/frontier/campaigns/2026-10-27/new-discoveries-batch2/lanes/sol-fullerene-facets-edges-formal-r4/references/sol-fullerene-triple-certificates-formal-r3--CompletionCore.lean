import RealCore
import Rank
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TripleCertificates
open FullereneGeometry
theorem sorted_active {q : Fin 32 → E} {x : E} (ids : Fin 3 → Fin 32)
 (hi : LinearIndependent ℝ (fun k => q (ids k))) (ha : ∀ k, dot (q (ids k)) x = 1) :
 ∃ i j k : Fin 32, i<j ∧ j<k ∧ dot (q i) x=1 ∧ dot (q j) x=1 ∧ dot (q k) x=1 := by
 have hinj : Function.Injective ids := by
  intro i j he
  apply hi.injective
  exact congrArg q he
 have h01 : ids 0 ≠ ids 1 := fun h => (by norm_num : (0:Fin 3) ≠ 1) (hinj h)
 have h02 : ids 0 ≠ ids 2 := fun h => (by norm_num : (0:Fin 3) ≠ 2) (hinj h)
 have h12 : ids 1 ≠ ids 2 := fun h => (by norm_num : (1:Fin 3) ≠ 2) (hinj h)
 rcases lt_or_gt_of_ne h01 with h01 | h10
 · rcases lt_or_gt_of_ne h12 with h12 | h21
   · exact ⟨ids 0,ids 1,ids 2,h01,h12,ha 0,ha 1,ha 2⟩
   · rcases lt_or_gt_of_ne h02 with h02 | h20
     · exact ⟨ids 0,ids 2,ids 1,h02,h21,ha 0,ha 2,ha 1⟩
     · exact ⟨ids 2,ids 0,ids 1,h20,h01,ha 2,ha 0,ha 1⟩
 · rcases lt_or_gt_of_ne h02 with h02 | h20
   · exact ⟨ids 1,ids 0,ids 2,h10,h02,ha 1,ha 0,ha 2⟩
   · rcases lt_or_gt_of_ne h12 with h12 | h21
     · exact ⟨ids 1,ids 2,ids 0,h12,h20,ha 1,ha 2,ha 0⟩
     · exact ⟨ids 2,ids 1,ids 0,h21,h10,ha 2,ha 1,ha 0⟩
theorem binding_dot (q : Fin 32 → E) (A : Fin 32 → V) (D : ℤ)
 (hq : ∀ i, rv (A i) = (D:ℝ) • q i) (i : Fin 32) (x : E) :
 dot (rv (A i)) x = (D:ℝ)*dot (q i) x := by
 rw [hq i]
 simp [dot, Finset.mul_sum, mul_assoc]
theorem complete_real (q : Fin 32 → E) (p : Fin 60 → E)
 (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point) (rs : List Certificate)
 (hD : (0:ℝ) < D) (hq : ∀ i, rv (A i) = (D:ℝ) • q i)
 (hp : ∀ v, rp (P v) = p v) (hcheck : ∀ r∈rs, checked A D P r)
 (hcover : rs.map Certificate.ids = triples)
 (ids : Fin 3 → Fin 32) (hi : LinearIndependent ℝ (fun k => q (ids k)))
 (x : E) (hf : x ∈ poly q) (ha : ∀ k, dot (q (ids k)) x = 1) : x ∈ Set.range p := by
 obtain ⟨i,j,k,hij,hjk,hai,haj,hak⟩ := sorted_active ids hi ha
 have hfeas : ∀ t, dot (rv (A t)) x ≤ (D:ℝ) := by
  intro t
  rw [binding_dot q A D hq]
  simpa using mul_le_mul_of_nonneg_left (hf t) hD.le
 have act : ∀ t, dot (q t) x = 1 → dot (rv (A t)) x = (D:ℝ) := by
  intro t ht
  rw [binding_dot q A D hq, ht, mul_one]
 obtain ⟨v,hv⟩ := covered_real A D P rs hcheck hcover i j k hij hjk x hfeas (act i hai) (act j haj) (act k hak)
 exact ⟨v, (hp v).symm.trans hv⟩
theorem listed_real (q : Fin 32 → E) (A : Fin 32 → V) (D : ℤ) (p : Point)
 (hD : (0:ℝ) < D) (hq : ∀ i, rv (A i) = (D:ℝ) • q i)
 (i j k : Fin 32) (h : core (A i) (A j) (A k) D p)
 (hf : ∀ t, dp (A t) p.num ≤ D*p.den) :
 rp p ∈ poly q ∧ ∃ ids : Fin 3 → Fin 32,
 (∀ t, dot (q (ids t)) (rp p) = 1) ∧
 (∀ y : E, (∀ t, dot (q (ids t)) y = 1) → y = rp p) := by
 have act : ∀ t, active (A t) D p → dot (q t) (rp p) = 1 := by
  intro t ht
  have hh := active_real (A t) D p h.1 ht
  rw [binding_dot q A D hq] at hh
  nlinarith
 constructor
 · intro t
   have hd : (0:ℝ) < p.den := by exact_mod_cast h.1
   have ht : dot (rv (A t)) (rp p) ≤ (D:ℝ) := by
    rw [dot_rp]
    apply (div_le_iff₀ hd).mpr
    exact_mod_cast hf t
   rw [binding_dot q A D hq] at ht
   nlinarith
 · refine ⟨![i,j,k], ?_, ?_⟩
   · intro t; fin_cases t
     · exact act i h.2.2.1
     · exact act j h.2.2.2.1
     · exact act k h.2.2.2.2
   · intro y hy
     apply core_unique (A i) (A j) (A k) D p h y
     · rw [binding_dot q A D hq]; simpa using congrArg (fun a : ℝ => (D:ℝ)*a) (hy 0)
     · rw [binding_dot q A D hq]; simpa using congrArg (fun a : ℝ => (D:ℝ)*a) (hy 1)
     · rw [binding_dot q A D hq]; simpa using congrArg (fun a : ℝ => (D:ℝ)*a) (hy 2)
end TripleCertificates

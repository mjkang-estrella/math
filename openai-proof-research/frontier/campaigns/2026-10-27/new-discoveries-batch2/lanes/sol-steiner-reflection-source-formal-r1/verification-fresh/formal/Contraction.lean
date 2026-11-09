import CutTensor
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
namespace SteinerReflection
open scoped BigOperators
open Finset
noncomputable section
def A (h l : V) : ℝ := 1/15-delta h l
def Ax (x : V → ℝ) (h : V) := ∑ l, A h l*x l
def C (i j k l : V) : ℝ := ∑ h, M i j k h*A h l
def H (x : V → ℝ) (i : V) : ℝ := ∑ j, ∑ k, ∑ l, C i j k l*x j*x k*x l
lemma Ax_eq (x : V → ℝ) (h : V) : Ax x h = (∑ l,x l)/15-x h := by
  classical
  simp only [Ax,A,sub_mul,Finset.sum_sub_distrib]
  simp [delta,←Finset.mul_sum,div_eq_mul_inv]; ring
lemma H_mixed (x : V → ℝ) (i : V) : H x i =
    ∑ j, ∑ k, ∑ h, M i j k h*x j*x k*Ax x h := by
  unfold H C Ax
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro k _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro h _
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro l _; ring
lemma H_cut (x : V → ℝ) (i : V) : H x i =
    ∑ a ∈ leaves, ((∑ j,x j)^2*(∑ h,Ax x h)-delta a i*(x a)^2*Ax x a-
      (1-delta a i)*((∑ j,x j)-x a)^2*((∑ h,Ax x h)-Ax x a)) := by
  rw [H_mixed]
  simp_rw [minimum_cut,Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := univ) (t := leaves)]
  apply sum_congr rfl; intro a _
  exact cut_contraction a i x (Ax x)
def x (s : ℝ) (i : V) : ℝ := if i = 0 then s+29 else -1
lemma sum_x (s : ℝ) : ∑ i,x s i = s := by
  classical
  have hx (i : V) : x s i = (if i = 0 then s+30 else 0)-1 := by
    by_cases hi : i = 0 <;> simp [x,hi] ; ring
  simp_rw [hx,sum_sub_distrib]
  simp
lemma sum_Ax (s : ℝ) : ∑ i,Ax (x s) i = s := by
  simp_rw [Ax_eq,sum_x]
  simp [sum_sub_distrib,sum_x]; ring
lemma orbit_contraction (s : ℝ) (i : V) : H (x s) i =
    if i = 0 then 29*(s^3-(s+1)^2*(14*s/15-1)) else
      28*(s^3-(s+1)^2*(14*s/15-1))+(s^3-s/15-1) := by
  classical
  rw [H_cut]
  simp_rw [sum_x,sum_Ax,Ax_eq,sum_x]
  have ha (a : V) (ha : a ∈ leaves) : x s a = -1 := by
    simp only [leaves,mem_erase,mem_univ,and_true] at ha
    simp [x,ha]
  simp_rw [show (∑ a ∈ leaves,
    (s^2*s-delta a i*(x s a)^2*(s/15-x s a)-
     (1-delta a i)*(s-x s a)^2*(s-(s/15-x s a)))) =
    ∑ a ∈ leaves, (s^3-delta a i*(s/15+1)-(1-delta a i)*(s+1)^2*(14*s/15-1)) by
      apply sum_congr rfl; intro a hh; rw [ha a hh]; ring]
  by_cases hi : i = 0
  · subst i
    have hh (a : V) (ha : a ∈ leaves) : delta a 0 = 0 := by
      simp only [leaves,mem_erase,mem_univ,and_true] at ha
      simp [delta,Ne.symm ha]
    trans ∑ a ∈ leaves, (s^3-(s+1)^2*(14*s/15-1))
    · apply sum_congr rfl; intro a ha; rw [hh a ha]; ring
    · simp [leaves]; ring
  · have him : i ∈ leaves := by simp [leaves,hi]
    rw [ite_eq_right hi,←sum_erase_add _ _ him]
    have hh (a : V) (ha : a ∈ leaves.erase i) : delta a i = 0 := by
      simp only [mem_erase] at ha
      simp [delta,Ne.symm ha.1]
    have hs : (∑ a ∈ leaves.erase i,
      (s^3-delta a i*(s/15+1)-(1-delta a i)*(s+1)^2*(14*s/15-1))) =
      28*(s^3-(s+1)^2*(14*s/15-1)) := by
        trans ∑ a ∈ leaves.erase i, (s^3-(s+1)^2*(14*s/15-1))
        · apply sum_congr rfl; intro a ha; rw [hh a ha]; ring
        · rw [sum_const,card_erase_of_mem him]; norm_num [leaves]
    rw [hs]; simp [delta]; ring
end
end SteinerReflection

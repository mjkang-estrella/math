import StarMinimum
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace SteinerReflection
open scoped BigOperators
noncomputable section
open Finset
def delta (a i : V) : ℝ := if i = a then 1 else 0
def cut (a i j k h : V) : ℝ := 1-delta a i*delta a j*delta a k*delta a h-
  (1-delta a i)*(1-delta a j)*(1-delta a k)*(1-delta a h)
def M (i j k h : V) : ℝ := minimumDistance ![i,j,k,h]
lemma cut_indicator (a i j k h : V) : cut a i j k h =
    if ((∃ b : Fin 4, (![i,j,k,h] : Fin 4 → V) b = a) ∧
       (∃ b : Fin 4, (![i,j,k,h] : Fin 4 → V) b ≠ a)) then 1 else 0 := by
  classical
  simp only [Fin.exists_fin_succ,Fin.exists_fin_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ,or_false]
  by_cases hi : i = a <;> by_cases hj : j = a <;> by_cases hk : k = a <;>
    by_cases hh : h = a <;> simp [cut,delta,hi,hj,hk,hh]
lemma minimum_cut (i j k h : V) : M i j k h = ∑ a ∈ leaves, cut a i j k h := by
  classical
  simp only [M,minimumDistance_eq,required,Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero,cut_indicator]
lemma sum_product (f g h : V → ℝ) :
    (∑ j, ∑ k, ∑ l, f j*g k*h l) = (∑ j, f j)*(∑ k,g k)*(∑ l,h l) := by
  simp only [←Finset.mul_sum,←Finset.sum_mul]
lemma cut_contraction (a i : V) (x y : V → ℝ) :
    (∑ j, ∑ k, ∑ h, cut a i j k h*x j*x k*y h) =
    (∑ j,x j)^2*(∑ h,y h) - delta a i*(x a)^2*y a -
      (1-delta a i)*((∑ j,x j)-x a)^2*((∑ h,y h)-y a) := by
  classical
  have term (j k h : V) : cut a i j k h*x j*x k*y h =
      x j*x k*y h - delta a i*((delta a j*x j)*(delta a k*x k)*(delta a h*y h))-
      (1-delta a i)*(((1-delta a j)*x j)*((1-delta a k)*x k)*((1-delta a h)*y h)) := by
    unfold cut; ring
  simp_rw [term, Finset.sum_sub_distrib, ←Finset.mul_sum]
  simp only [←Finset.sum_mul, ←Finset.mul_sum]
  have hd (z : V → ℝ) : ∑ j, delta a j*z j = z a := by
    simp [delta]
  have hc (z : V → ℝ) : ∑ j, (1-delta a j)*z j = (∑ j,z j)-z a := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib]; rw [hd]
  rw [hd,hd,hc,hc]; ring
end
end SteinerReflection

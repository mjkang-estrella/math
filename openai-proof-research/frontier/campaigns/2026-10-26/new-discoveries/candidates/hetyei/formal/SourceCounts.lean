import SourceCompositions
import RenewalTail

open Finset
namespace FlatBernoulli
noncomputable section

def sourceK (n : ℕ) : ℝ := ∑ c : Composition n,
  if ∀ b ∈ c.blocks, 2 ≤ b then
    (n.factorial:ℝ) / (c.blocks.map (fun b => (b.factorial:ℝ))).prod *
      (c.blocks.map (fun b => ((b-2).factorial:ℝ))).prod
  else 0

theorem blockWeight_factorial_ratio (b : ℕ) (hb : 2 ≤ b) :
    blockWeight b = ((b-2).factorial:ℝ)/(b.factorial:ℝ) := by
  obtain ⟨k,rfl⟩ : ∃ k, b=k+2 := ⟨b-2,by omega⟩
  have hf : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [blockWeight,show 2 ≤ k+2 by omega,ite_true,
    Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp [hf]
  rw [show (k+2-1:ℕ)=k+1 by omega]
  push_cast
  ring

theorem composition_ratio_product (l : List ℕ) (hl : ∀ b ∈ l, 2 ≤ b) :
    (l.map (fun b => ((b-2).factorial:ℝ))).prod /
      (l.map (fun b => (b.factorial:ℝ))).prod = (l.map blockWeight).prod := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [mul_div_mul_comm,ih (fun j hj => hl j (List.mem_cons_of_mem b hj)),
      ← blockWeight_factorial_ratio b (hl b (by simp))]

theorem sourceK_normalized (n : ℕ) :
    sourceK n = (n.factorial:ℝ)*normalizedComposition n := by
  unfold sourceK normalizedComposition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · rw [← composition_ratio_product c.blocks hc]
    ring
  · obtain ⟨b,hb,hbad⟩ := by simpa only [not_forall,not_imp] using hc
    have hw : blockWeight b = 0 := by simp [blockWeight,hbad]
    have hz : (c.blocks.map blockWeight).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨b,hb,hw⟩)
    rw [hz,mul_zero]

theorem sourceK_eq_renewal (n : ℕ) : sourceK n = (n.factorial:ℝ)*renewalCoefficient n := by
  rw [sourceK_normalized,normalizedComposition_eq_renewal]

/-- Exact adjacent-count inequality in the source's finite composition formula. -/
theorem source_K_tail (n : ℕ) (hn : 11 ≤ n) : sourceK n < (n:ℝ)*sourceK (n-1) := by
  have h := renewal_tail_negative n hn
  change renewalCoefficient n-renewalCoefficient (n-1) < 0 at h
  have hn1 : 1 ≤ n := by omega
  have hf : (n.factorial:ℝ) = (n:ℝ)*((n-1).factorial:ℝ) := by
    have hn' : n=(n-1)+1 := by omega
    nth_rw 1 [hn']
    rw [Nat.factorial_succ]
    push_cast
    rw [show ((n-1:ℕ):ℝ)+1=(n:ℝ) by exact_mod_cast hn'.symm]
  have hpos : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [sourceK_eq_renewal,sourceK_eq_renewal]
  calc
    _ < (n.factorial:ℝ)*renewalCoefficient (n-1) :=
      mul_lt_mul_of_pos_left (by linarith) hpos
    _ = _ := by rw [hf];ring

/-- The relation kappa_(n+1)=(n+1)K_n is the source's proved count formula. -/
def sourceKappa (n : ℕ) : ℝ := (n:ℝ)*sourceK (n-1)

/-- Hetyei Conjecture6.10, rank>=12, on its literal finite count presentation. -/
theorem source_conjecture_319292 (n : ℕ) (hn : 12 ≤ n) :
    sourceKappa n < (n:ℝ)*sourceKappa (n-1) := by
  have h := source_K_tail (n-1) (by omega)
  unfold sourceKappa
  have he : n-1-1 = n-2 := by omega
  rw [he]
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb := mul_lt_mul_of_pos_left h hnpos
  simpa only [show n-1-1 = n-2 by omega,mul_assoc] using hb

end
end FlatBernoulli

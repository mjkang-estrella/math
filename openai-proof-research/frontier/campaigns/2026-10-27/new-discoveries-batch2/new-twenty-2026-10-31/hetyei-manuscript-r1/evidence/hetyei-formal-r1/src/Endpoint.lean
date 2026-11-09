import Compute
import Mathlib.Tactic.Abel
namespace Hetyei347230
theorem star_single (w : Word) (c : ℚ) :
    star (Finsupp.single w c) = Finsupp.single w.reverse c := by
  simp [star]
theorem star_involution (p : ABPoly) : star (star p) = p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single w c => simp [star_single]

theorem toPoly_degree (l : FSum) (n : ℕ) (h : ∀ p ∈ l, p.1.length = n) :
    toPoly l ∈ deg n := by
  induction l with
  | nil => simp [toPoly]
  | cons p l ih =>
    rw [toPoly_cons]
    apply Submodule.add_mem
    · apply Finsupp.single_mem_supported
      exact h p (by simp)
    · apply ih
      intro q hq
      exact h q (by simp [hq])

theorem uCert_deg : uCert ∈ deg 5 := by
  apply toPoly_degree
  intro p hp
  simp only [uList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> subst p <;> rfl

theorem star_uCert : star uCert = uCert := by
  simp only [uCert, uList, toPoly, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, map_add, map_zero, star_single]
  simp only [a, b, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  abel

theorem uCert_ne_zero : uCert ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ABPoly => p [a,a,a,b,a]) h
  rw [uCert, toPoly_coeff] at hc
  norm_num [coeffL, uList, a, b] at hc

theorem kernel_conjecture_false : ¬ KernelConjecture := by
  intro h
  have hmem : uCert ∈ deg 5 ⊓ LinearMap.ker I2 :=
    ⟨uCert_deg, by simpa using I2_uCert⟩
  rw [h 5 (by norm_num)] at hmem
  have hanti : star uCert + uCert = 0 := by simpa [anti] using hmem.2
  rw [star_uCert] at hanti
  have hz : (2 : ℚ) • uCert = 0 := by rw [two_smul]; exact hanti
  exact uCert_ne_zero ((smul_eq_zero.mp hz).resolve_left (by norm_num))
end Hetyei347230

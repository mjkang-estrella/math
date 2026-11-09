import LiteralDifferential

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

def hankelDivided (i : Fin 2) (l : ℕ) : QPoly :=
  MvPolynomial.C (1/(l.factorial : ℚ))*hankelNumerator i l
def a (i : Fin 2) (l : ℕ) : G := coeffEmbed (hankelDivided i l)
def parameter (i : Fin 2) : G := coeffEmbed (MvPolynomial.X i)

theorem hankelNumerator_succ (i : Fin 2) (l : ℕ) :
    hankelNumerator i (l+1)=hankelNumerator i l *
      (MvPolynomial.X i-MvPolynomial.C ((l : ℚ)*((l : ℚ)+1))) := by
  simp only [hankelNumerator, Finset.prod_range_succ]

theorem hankelDivided_recurrence (i : Fin 2) (l : ℕ) :
    ((l+1 : ℕ) : QPoly)*hankelDivided i (l+1)=
      (MvPolynomial.X i-(l : QPoly)*((l : QPoly)+1))*hankelDivided i l := by
  have hn : ((l+1 : ℕ) : ℚ)*(1/((l+1).factorial : ℚ))=1/(l.factorial : ℚ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h0 : (l.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero l
    have h1 : ((l+1 : ℕ) : ℚ)≠0 := by exact_mod_cast Nat.succ_ne_zero l
    field_simp
  simp only [hankelDivided, hankelNumerator_succ]
  calc
    _ = MvPolynomial.C (((l+1 : ℕ) : ℚ)*(1/((l+1).factorial : ℚ))) *
      hankelNumerator i l * (MvPolynomial.X i-MvPolynomial.C ((l : ℚ)*((l : ℚ)+1))) := by
        simp only [map_mul, map_natCast]
        ring
    _ = _ := by rw [hn]; simp only [map_mul, map_add, map_natCast, map_one]; ring

theorem a_recurrence (i : Fin 2) (l : ℕ) :
    ((l+1 : ℕ) : G)*a i (l+1)=(parameter i-(l : G)*((l : G)+1))*a i l := by
  have h := congrArg coeffEmbed (hankelDivided_recurrence i l)
  simpa only [map_mul, map_sub, map_add, map_natCast, map_one, a, parameter] using h

@[simp] theorem deltaG_a (i : Fin 2) (l : ℕ) : deltaG (a i l)=0 :=
  deltaG_coeffEmbed _

theorem C_divided (s : ℕ) :
    C s=∑ l ∈ Finset.range (s+1), a 0 l*a 1 (s-l)*xi^l*eta^(s-l) := by
  unfold C literalC
  apply Finset.sum_congr rfl
  intro l _
  simp only [a, hankelDivided, one_div, mul_inv_rev, map_mul]
  ring

theorem deltaG_monomial (c : G) (hc : deltaG c=0) (l m : ℕ) :
    deltaG (c*xi^l*eta^m)=imaginaryUnit*c*xi^l*eta^m*
      ((l : G)*(xi-1)+(m : G)*(eta-1)) := by
  simp only [deltaG_mul, hc, deltaG_logistic_pow xi deltaG_xi,
    deltaG_logistic_pow eta deltaG_eta]
  ring

theorem deltaG_monomial_second (c : G) (hc : deltaG c=0) (l m : ℕ) :
    deltaG (deltaG (c*xi^l*eta^m)) +
      imaginaryUnit*((l : G)+(m : G))*deltaG (c*xi^l*eta^m) =
    -(c*xi^l*eta^m)*((l : G)*((l : G)+1)*xi*(xi-1)+
      (m : G)*((m : G)+1)*eta*(eta-1)) := by
  rw [deltaG_monomial c hc l m]
  simp only [deltaG_mul, deltaG_imaginaryUnit, hc, deltaG_natCast,
    deltaG_logistic_pow xi deltaG_xi, deltaG_logistic_pow eta deltaG_eta,
    map_add, map_sub, deltaG_one, deltaG_xi, deltaG_eta, mul_zero, zero_mul, zero_add, sub_zero]
  have hcurve := xi_eta_curve
  linear_combination
    (c*xi^l*eta^m*((l : G)*(xi-1)+(m : G)*(eta-1))^2 +
      c*xi^l*eta^m*((l : G)*xi*(xi-1)+(m : G)*eta*(eta-1)) +
      c*xi^l*eta^m*((l : G)+(m : G))*((l : G)*(xi-1)+(m : G)*(eta-1))) *
        imaginaryUnit_sq - c*xi^l*eta^m*(l : G)*(m : G)*hcurve

def dxTerm (s l : ℕ) : G :=
  (l : G)*a 0 l*a 1 (s-l)*xi^l*(xi-1)*eta^(s-l)
def dyTerm (s l : ℕ) : G :=
  ((s-l : ℕ) : G)*a 0 l*a 1 (s-l)*xi^l*eta^(s-l)*(eta-1)

theorem deltaG_C_split (s : ℕ) : deltaG (C s)=imaginaryUnit*
    ((∑ l ∈ Finset.range (s+1), dxTerm s l)+(∑ l ∈ Finset.range (s+1), dyTerm s l)) := by
  rw [C_divided, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [deltaG_monomial _ (by simp [deltaG_mul])]
  dsimp [dxTerm, dyTerm]
  ring

theorem dxTerm_shift (s : ℕ) :
    (∑ l ∈ Finset.range (s+1+1), dxTerm (s+1) l)=
    ∑ l ∈ Finset.range (s+1),
      (parameter 0-(l : G)*((l : G)+1))*a 0 l*a 1 (s-l)*
        xi^(l+1)*(xi-1)*eta^(s-l) := by
  rw [Finset.sum_range_succ']
  simp only [dxTerm, Nat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Nat.add_sub_add_right]
  calc
    _ = (((l+1 : ℕ) : G)*a 0 (l+1))*a 1 (s-l)*xi^(l+1)*(xi-1)*eta^(s-l) := by ring
    _ = _ := by rw [a_recurrence]

theorem dyTerm_shift (s : ℕ) :
    (∑ l ∈ Finset.range (s+1+1), dyTerm (s+1) l)=
    ∑ l ∈ Finset.range (s+1),
      (parameter 1-((s-l : ℕ) : G)*(((s-l : ℕ) : G)+1))*a 0 l*a 1 (s-l)*
        xi^l*eta^(s-l+1)*(eta-1) := by
  rw [Finset.sum_range_succ]
  simp only [dyTerm, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  have hm : s+1-l=s-l+1 := by have := Finset.mem_range.mp hl; omega
  rw [hm]
  calc
    _ = a 0 l*((((s-l+1 : ℕ) : G))*a 1 (s-l+1))*xi^l*eta^(s-l+1)*(eta-1) := by ring
    _ = _ := by rw [a_recurrence]; ring

theorem deltaG_C_next (s : ℕ) : deltaG (C (s+1))=imaginaryUnit*
    (∑ l ∈ Finset.range (s+1), a 0 l*a 1 (s-l)*xi^l*eta^(s-l)*
      ((parameter 0-(l : G)*((l : G)+1))*xi*(xi-1)+
       (parameter 1-((s-l : ℕ) : G)*(((s-l : ℕ) : G)+1))*eta*(eta-1))) := by
  rw [deltaG_C_split, dxTerm_shift, dyTerm_shift, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_succ, pow_succ]
  ring

def potentialCurve : G := -(parameter 0*xi*(xi-1)+parameter 1*eta*(eta-1))

theorem deltaG_C_second (s : ℕ) :
    deltaG (deltaG (C s))+imaginaryUnit*(s : G)*deltaG (C s)=
    ∑ l ∈ Finset.range (s+1),
      -(a 0 l*a 1 (s-l)*xi^l*eta^(s-l))*
        ((l : G)*((l : G)+1)*xi*(xi-1)+
          ((s-l : ℕ) : G)*(((s-l : ℕ) : G)+1)*eta*(eta-1)) := by
  simp only [C_divided, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hs : (s : G)=(l : G)+((s-l : ℕ) : G) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le (by have := Finset.mem_range.mp hl; omega)]
  rw [hs]
  exact deltaG_monomial_second _ (by simp [deltaG_mul]) _ _

theorem imaginaryUnit_twice (z : G) : imaginaryUnit*(imaginaryUnit*z)= -z := by
  calc
    _ = imaginaryUnit^2*z := by ring
    _ = -z := by rw [imaginaryUnit_sq]; ring

/-- The Hankel differential equation follows from the finite product recurrence.
There is no differential-equation hypothesis in this theorem. -/
theorem literal_hankel_R1 (s : ℕ) :
    deltaG (deltaG (C s))+imaginaryUnit*(s : G)*deltaG (C s)+
      imaginaryUnit*deltaG (C (s+1))-potentialCurve*C s=0 := by
  rw [deltaG_C_second, deltaG_C_next, imaginaryUnit_twice,
    sub_eq_add_neg, C_divided,
    Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  dsimp [potentialCurve]
  ring

end JacobiShifted.SourceBridge

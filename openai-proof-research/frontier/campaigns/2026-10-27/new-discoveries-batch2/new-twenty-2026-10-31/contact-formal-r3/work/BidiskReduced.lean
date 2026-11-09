import CayleyPolynomials
namespace ContactPilot
noncomputable section
open MvPolynomial
set_option linter.unusedSimpArgs false
private abbrev J : Poly₂ := C Complex.I
private def fm : Poly₂ := J*(1-W)*(J*(1-Z)) - J*(1-W)*(1+Z) - (1+Z)*(1+W)
private def fp : Poly₂ := J*(1-W)*(J*(1-Z)) + J*(1-W)*(1+Z) - (1+Z)*(1+W)
private abbrev k : MvPolynomial (Fin 1) ℂ := X 0
private abbrev jm : MvPolynomial (Fin 1) ℂ := C Complex.I
private def u (s : ℂ) : MvPolynomial (Fin 1) ℂ := C (-2-s*Complex.I)*k + C (s*Complex.I)
private def v (s : ℂ) : MvPolynomial (Fin 1) ℂ := C (-s*Complex.I)*k + C (-2+s*Complex.I)
private theorem uv_coprime (s : ℂ) (hs : s^2 = 1) : IsCoprime (u s) (v s) := by
  refine ⟨C (s*Complex.I/4), C ((-2-s*Complex.I)/4), ?_⟩
  simp only [u,v, mul_add, ←map_mul, ←map_add, ←map_one C]
  ring_nf
  simp [←map_pow, ←map_mul, ←map_add, Complex.I_sq, hs]
private theorem u_ne_zero (s : ℂ) (hs : s ≠ 0) : u s ≠ 0 := by
  intro h
  have he := congrArg (eval (fun _ : Fin 1 => (0:ℂ))) h
  simpa [u, mul_ne_zero hs Complex.I_ne_zero] using he
private theorem mapped_fm :
    MvPolynomial.finSuccEquiv ℂ 1 fm = Polynomial.C (u (-1)) * Polynomial.X + Polynomial.C (v (-1)) := by
  simp only [fm, J, Z, W, map_sub, map_mul, map_add, map_one,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simp [u, v, k, finSuccEquiv_apply]
  ring_nf
  norm_num [←map_pow, ←map_mul, ←map_add, Complex.I_sq]
private theorem mapped_fp :
    MvPolynomial.finSuccEquiv ℂ 1 fp = Polynomial.C (u 1) * Polynomial.X + Polynomial.C (v 1) := by
  simp only [fp, J, Z, W, map_sub, map_mul, map_add, map_one,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simp [u, v, k, finSuccEquiv_apply]
  ring_nf
  norm_num [←map_pow, ←map_mul, ←map_add, Complex.I_sq]
end
end ContactPilot

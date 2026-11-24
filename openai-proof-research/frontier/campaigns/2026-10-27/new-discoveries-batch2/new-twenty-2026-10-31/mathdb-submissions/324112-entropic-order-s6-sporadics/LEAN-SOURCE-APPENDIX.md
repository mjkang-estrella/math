# Lean source appendix

### `EntropicDefinitions.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Real BigOperators
namespace McConnell

noncomputable def cmi (M : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  (∑ i, negMulLog (∑ j, M i j)) + (∑ j, negMulLog (∑ i, M i j))
    - ∑ i, ∑ j, negMulLog (M i j)

def InD6 (p : Fin 6 → ℝ) : Prop :=
  (∀ i j, i ≤ j → p j ≤ p i) ∧ 0 ≤ p 5 ∧ ∑ i, p i = 1

def M11 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 1, p 3; p 5, p 2, p 4]
def M37 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 2, p 5; p 1, p 3, p 4]
def M43 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 3, p 4; p 1, p 2, p 5]
def M49 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 3, p 5; p 1, p 2, p 4]

noncomputable def phi (x : ℝ) : ℝ := x * Real.log x
noncomputable def marginalPhi (a b c d e f : ℝ) : ℝ :=
  phi (a+b+c) + phi (d+e+f) + phi (a+d) + phi (b+e) + phi (c+f)
noncomputable def gap37 (p : Fin 6 → ℝ) : ℝ :=
  marginalPhi (p 0) (p 2) (p 5) (p 1) (p 3) (p 4) -
  marginalPhi (p 0) (p 1) (p 3) (p 5) (p 2) (p 4)
noncomputable def gap43 (p : Fin 6 → ℝ) : ℝ :=
  marginalPhi (p 0) (p 3) (p 4) (p 1) (p 2) (p 5) -
  marginalPhi (p 0) (p 1) (p 3) (p 5) (p 2) (p 4)
noncomputable def gap49 (p : Fin 6 → ℝ) : ℝ :=
  marginalPhi (p 0) (p 3) (p 5) (p 1) (p 2) (p 4) -
  marginalPhi (p 0) (p 1) (p 3) (p 5) (p 2) (p 4)

theorem cmi_gap37 (p : Fin 6 → ℝ) :
    cmi (M11 p) - cmi (M37 p) = gap37 p := by
  simp [cmi, M11, M37, gap37, marginalPhi, phi, Real.negMulLog,
    Fin.sum_univ_succ]
  ring

theorem cmi_gap43 (p : Fin 6 → ℝ) :
    cmi (M11 p) - cmi (M43 p) = gap43 p := by
  simp [cmi, M11, M43, gap43, marginalPhi, phi, Real.negMulLog,
    Fin.sum_univ_succ]
  ring

theorem cmi_gap49 (p : Fin 6 → ℝ) :
    cmi (M11 p) - cmi (M49 p) = gap49 p := by
  simp [cmi, M11, M49, gap49, marginalPhi, phi, Real.negMulLog,
    Fin.sum_univ_succ]
  ring

theorem InD6_uniform : InD6 (fun _ : Fin 6 => (1 : ℝ)/6) := by
  constructor
  · intro i j hij
    exact le_refl _
  constructor
  · norm_num
  · norm_num [Fin.sum_univ_succ]

/-- The exact required endpoint reduces to three gap inequalities, with no
additional analytic or positivity hypotheses in the bridge. -/
theorem endpoint_iff (p : Fin 6 → ℝ) :
    (cmi (M37 p) ≤ cmi (M11 p) ∧ cmi (M43 p) ≤ cmi (M11 p) ∧
      cmi (M49 p) ≤ cmi (M11 p)) ↔
    (0 ≤ gap37 p ∧ 0 ≤ gap43 p ∧ 0 ≤ gap49 p) := by
  rw [← cmi_gap37, ← cmi_gap43, ← cmi_gap49]
  simp only [sub_nonneg]

noncomputable def F (A c d e f : ℝ) : ℝ :=
  phi (A+c+f)+phi (A+d+e)+phi (2*A)+phi (c+d)+phi (e+f)
  -phi (2*A+d)-phi (c+e+f)-phi (A+f)-phi (A+c)-phi (d+e)

noncomputable def J (A D e : ℝ) : ℝ :=
  phi (A+D+e)+phi (2*A)+phi (2*D)+phi e
  -phi (2*A+D)-phi (D+e)-phi A-phi (D+e)

noncomputable def G (A C E : ℝ) : ℝ :=
  2*phi (A+C+E)+phi (2*A)+phi (2*C)+phi (2*E)
  -phi (2*A+C)-phi (C+2*E)-phi (A+E)-phi (A+C)-phi (C+E)

theorem F_zero_last (A c d e : ℝ) :
    F A c d e 0 = phi (A+d+e)+phi (2*A)+phi (c+d)+phi e
      -phi (2*A+d)-phi (c+e)-phi A-phi (d+e) := by
  simp [F]
  ring

theorem F_J (A D e : ℝ) : F A D D e 0 = J A D e := by
  rw [F_zero_last]
  unfold J
  congr 1
  ring

theorem F_G (A C E : ℝ) : F A C C E E = G A C E := by
  unfold F G
  have h : C+E+E = C+2*E := by ring
  rw [h]
  have hC : C+C = 2*C := by ring
  have hE : E+E = 2*E := by ring
  rw [hC, hE]
  ring

#print axioms cmi_gap37
#print axioms cmi_gap43
#print axioms cmi_gap49
#print axioms InD6_uniform
#print axioms endpoint_iff
#print axioms F_J
#print axioms F_G
end McConnell
```

### `EntropicEnvelope.lean`

```lean
import EntropicDefinitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Real Set
namespace McConnell

theorem phi_comp_hasDerivAt {u : ℝ → ℝ} {x du : ℝ}
    (hu : HasDerivAt u du x) (hpos : 0 < u x) :
    HasDerivAt (fun t => phi (u t)) ((log (u x)+1)*du) x :=
  (Real.hasDerivAt_mul_log hpos.ne').comp x hu

/-- Chain rule before the critical-point cancellation. -/
theorem J_path_hasDerivAt {e : ℝ → ℝ} {A D de : ℝ}
    (hA : 0 < A) (hD : 0 < D) (he : 0 < e A)
    (hd : HasDerivAt e de A) :
    HasDerivAt (fun t => J t D (e t))
      ((log (A+D+e A)+2*log (2*A)-2*log (2*A+D)-log A) +
       de*(log (A+D+e A)+log (e A)-2*log (D+e A))) A := by
  have hi := hasDerivAt_id A
  have h1 := phi_comp_hasDerivAt ((hi.add_const D).add hd) (by positivity : 0 < A+D+e A)
  have h2 := phi_comp_hasDerivAt (hi.const_mul 2) (by positivity : 0 < 2*A)
  have h3 := (hasDerivAt_const A (phi (2*D)))
  have h4 := phi_comp_hasDerivAt hd he
  have h5 := phi_comp_hasDerivAt ((hi.const_mul 2).add_const D) (by positivity : 0 < 2*A+D)
  have h6 := phi_comp_hasDerivAt ((hasDerivAt_const A D).add hd) (by positivity : 0 < D+e A)
  have h7 := phi_comp_hasDerivAt hi hA
  have h := ((((((h1.add h2).add h3).add h4).sub h5).sub h6).sub h7).sub h6
  simp only [Pi.add_apply, id_eq] at h
  convert h using 1
  · rfl
  · ring

noncomputable def critical (A D : ℝ) : ℝ := D^2/(A-D)
noncomputable def envelope (D A : ℝ) : ℝ := J A D (critical A D)

theorem critical_pos {A D : ℝ} (hD : 0 < D) (hAD : D < A) :
    0 < critical A D := by
  unfold critical
  exact div_pos (sq_pos_of_pos hD) (sub_pos.mpr hAD)

theorem critical_identity {A D : ℝ} (hne : A-D ≠ 0) :
    critical A D * (A+D+critical A D) = (D+critical A D)^2 := by
  unfold critical
  field_simp [hne]
  ring

theorem critical_log_identity {A D : ℝ} (hD : 0 < D) (hAD : D < A) :
    log (A+D+critical A D)+log (critical A D)-2*log (D+critical A D) = 0 := by
  have he := critical_pos hD hAD
  have hA : 0 < A := lt_trans hD hAD
  have hS : 0 < A+D+critical A D := by positivity
  have hT : 0 < D+critical A D := by positivity
  have hh := congrArg log (critical_identity (sub_pos.mpr hAD).ne')
  rw [Real.log_mul he.ne' hS.ne', Real.log_pow] at hh
  norm_num at hh
  linarith

/-- Risk §3: actual HasDerivAt of M, not an assumed envelope rule. -/
theorem envelope_hasDerivAt {A D : ℝ} (hD : 0 < D) (hAD : D < A) :
    HasDerivAt (envelope D)
      (log (A+D+critical A D)+2*log (2*A)-2*log (2*A+D)-log A) A := by
  have hd : HasDerivAt (fun t : ℝ => critical t D)
      (-(D^2)/(A-D)^2) A := by
    unfold critical
    have hh := (hasDerivAt_const A (D^2)).div ((hasDerivAt_id A).sub_const D)
      (sub_pos.mpr hAD).ne'
    simp only [id_eq, zero_mul, mul_one, zero_sub] at hh
    exact hh
  have h := J_path_hasDerivAt (e := fun t => critical t D) (A := A) (D := D)
    (lt_trans hD hAD) hD (critical_pos hD hAD) hd
  rw [critical_log_identity hD hAD, mul_zero, add_zero] at h
  exact h

theorem envelope_derivative_nonneg {A D : ℝ} (hD : 0 < D) (hAD : D < A) :
    0 ≤ log (A+D+critical A D)+2*log (2*A)-2*log (2*A+D)-log A := by
  have hA : 0 < A := lt_trans hD hAD
  have he := critical_pos hD hAD
  have hs : 0 < A+D+critical A D := by positivity
  have ht : 0 < 2*A+D := by positivity
  have h2 : 0 < 2*A := by positivity
  have heq : A+D+critical A D = A^2/(A-D) := by
    unfold critical
    field_simp [(sub_pos.mpr hAD).ne']
    ring
  have hprod : (2*A+D)^2*A ≤ (A+D+critical A D)*(2*A)^2 := by
    rw [heq]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hAD)).2
    nlinarith [mul_nonneg (le_of_lt hA) (sq_nonneg D),
      mul_nonneg (sq_nonneg A) (sq_nonneg D)]
  have hl := Real.log_le_log (by positivity : 0 < (2*A+D)^2*A) hprod
  rw [Real.log_mul (pow_ne_zero 2 ht.ne') hA.ne',
    Real.log_mul hs.ne' (pow_ne_zero 2 h2.ne'),
    Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

theorem envelope_monotone {D : ℝ} (hD : 0 < D) :
    MonotoneOn (envelope D) (Ici (2*D)) := by
  have hd : ∀ t ∈ Ici (2*D), D < t := by
    intro t ht
    have hh : 2*D ≤ t := ht
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (fun t ht => (envelope_hasDerivAt hD (hd t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (envelope_hasDerivAt hD (hd t (interior_subset ht))).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(envelope_hasDerivAt hD (hd t (interior_subset ht))).deriv]
  exact envelope_derivative_nonneg hD (hd t (interior_subset ht))

theorem envelope_ge_face {A D : ℝ} (hD : 0 < D) (hAD : 2*D ≤ A) :
    J (2*D) D D ≤ envelope D A := by
  have he : critical (2*D) D = D := by
    unfold critical
    field_simp [hD.ne']
    ring
  have hh := envelope_monotone hD (mem_Ici.mpr le_rfl) (mem_Ici.mpr hAD) hAD
  simpa only [envelope, he] using hh

#print axioms envelope_monotone
#print axioms envelope_ge_face
#print axioms envelope_hasDerivAt
#print axioms envelope_derivative_nonneg
end McConnell
```

### `EntropicPath.lean`

```lean
import EntropicEnvelope

open Real Set
namespace McConnell
noncomputable def gA (A C : ℝ) : ℝ :=
  2*log (A+C+1)+2*log (2*A)-2*log (2*A+C)-log (A+1)-log (A+C)
noncomputable def gC (A C : ℝ) : ℝ :=
  2*log (A+C+1)+2*log (2*C)-log (2*A+C)-log (C+2)-log (A+C)-log (C+1)

theorem G_path_hasDerivAt {a c : ℝ → ℝ} {t da dc : ℝ}
    (ha : HasDerivAt a da t) (hc : HasDerivAt c dc t)
    (ha0 : 0 < a t) (hc0 : 0 < c t) :
    HasDerivAt (fun s => G (a s) (c s) 1) (da*gA (a t) (c t)+dc*gC (a t) (c t)) t := by
  have h1 := (phi_comp_hasDerivAt ((ha.add hc).add_const 1)
    (by positivity : 0 < a t+c t+1)).const_mul 2
  have h2 := phi_comp_hasDerivAt (ha.const_mul 2) (by positivity : 0 < 2*a t)
  have h3 := phi_comp_hasDerivAt (hc.const_mul 2) (by positivity : 0 < 2*c t)
  have h4 := hasDerivAt_const t (phi (2*1))
  have h5 := phi_comp_hasDerivAt ((ha.const_mul 2).add hc) (by positivity : 0 < 2*a t+c t)
  have h6 := phi_comp_hasDerivAt (hc.add_const (2*1)) (by positivity : 0 < c t+2*1)
  have h7 := phi_comp_hasDerivAt (ha.add_const 1) (by positivity : 0 < a t+1)
  have h8 := phi_comp_hasDerivAt (ha.add hc) (by positivity : 0 < a t+c t)
  have h9 := phi_comp_hasDerivAt (hc.add_const 1) (by positivity : 0 < c t+1)
  have h := (((((((h1.add h2).add h3).add h4).sub h5).sub h6).sub h7).sub h8).sub h9
  simp only [Pi.add_apply] at h
  convert h using 1
  · rfl
  · unfold gA gC
    ring

theorem path_lower_bound {A C : ℝ} (hAC : C ≤ A) (hC : 1 ≤ C) :
    max 1 (1/(A/C^2)) ≤ C := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hA0 : 0 < A := lt_of_lt_of_le hC0 hAC
  apply max_le hC
  rw [one_div_div]
  apply (div_le_iff₀ hA0).2
  nlinarith

theorem path_in_cone {k t : ℝ} (hk : 0 < k)
    (ht : max 1 (1/k) ≤ t) :
    1 ≤ t ∧ t ≤ k*t^2 := by
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hinv : 1/k ≤ t := le_trans (le_max_right _ _) ht
  have hkt : 1 ≤ k*t := by simpa only [mul_comm] using (div_le_iff₀ hk).mp hinv
  constructor
  · exact ht1
  · nlinarith

/-- §4.4, including both k-cases. The only remaining inputs are the explicit
weighted-gradient sign and the two edge inequalities; the path derivative itself
is supplied by G_path_hasDerivAt. -/
theorem G_nonneg_of_weighted_edges
    (hw : ∀ A C : ℝ, 1 ≤ C → C ≤ A → 0 ≤ 2*A*gA A C+C*gC A C)
    (hedge : ∀ A : ℝ, 1 ≤ A → 0 ≤ G A 1 1)
    (hdiag : ∀ C : ℝ, 1 ≤ C → 0 ≤ G C C 1)
    {A C : ℝ} (hAC : C ≤ A) (hC : 1 ≤ C) :
    0 ≤ G A C 1 := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hA0 : 0 < A := lt_of_lt_of_le hC0 hAC
  let k := A/C^2
  have hk : 0 < k := div_pos hA0 (sq_pos_of_pos hC0)
  let b := max 1 (1/k)
  have hbC : b ≤ C := path_lower_bound hAC hC
  have hb1 : 1 ≤ b := le_max_left _ _
  have hpath : ∀ t ∈ Icc b C, 1 ≤ t ∧ t ≤ k*t^2 := by
    intro t ht
    exact path_in_cone hk ht.1
  have hcont : Continuous (fun t : ℝ => G (k*t^2) t 1) := by
    unfold G phi
    fun_prop
  have hd : ∀ t ∈ interior (Icc b C),
      HasDerivAt (fun s : ℝ => G (k*s^2) s 1)
        ((2*k*t)*gA (k*t^2) t+gC (k*t^2) t) t := by
    intro t ht
    have htI := interior_subset ht
    have ht1 := (hpath t htI).1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hh := G_path_hasDerivAt
      (((hasDerivAt_id t).pow 2).const_mul k) (hasDerivAt_id t)
      (mul_pos hk (sq_pos_of_pos ht0)) ht0
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one] at hh
    convert hh using 1
    ring
  have hmono : MonotoneOn (fun t : ℝ => G (k*t^2) t 1) (Icc b C) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t ht).deriv]
    have htI := interior_subset ht
    have hcone := hpath t htI
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one hcone.1
    have hh := hw (k*t^2) t hcone.1 hcone.2
    have heq : (2*k*t)*gA (k*t^2) t+gC (k*t^2) t =
        (2*(k*t^2)*gA (k*t^2) t+t*gC (k*t^2) t)/t := by
      field_simp
    rw [heq]
    exact div_nonneg hh ht0.le
  have hedge0 : 0 ≤ G (k*b^2) b 1 := by
    by_cases hk1 : 1 ≤ k
    · have hi : 1/k ≤ 1 := (div_le_iff₀ hk).2 (by linarith)
      have hb : b = 1 := max_eq_left hi
      rw [hb]
      simpa using hedge k hk1
    · have hk1' : k ≤ 1 := le_of_lt (lt_of_not_ge hk1)
      have hi : 1 ≤ 1/k := (le_div_iff₀ hk).2 (by linarith)
      have hb : b = 1/k := max_eq_right hi
      have heq : k*b^2 = b := by
        rw [hb]
        field_simp
      rw [heq]
      exact hdiag b hb1
  have hm := hmono ⟨le_rfl, hbC⟩ ⟨hbC, le_rfl⟩ hbC
  have hend : k*C^2 = A := div_mul_cancel₀ A (pow_ne_zero 2 hC0.ne')
  change G (k*b^2) b 1 ≤ G (k*C^2) C 1 at hm
  rw [hend] at hm
  exact le_trans hedge0 hm

#print axioms G_path_hasDerivAt
#print axioms G_nonneg_of_weighted_edges
end McConnell
```

### `EntropicBoundary.lean`

```lean
import EntropicEnvelope

open Real Set Filter
open scoped Topology
namespace McConnell

theorem continuous_phi : Continuous phi := Real.continuous_mul_log

theorem nonneg_at_zero_of_pos {q : ℝ → ℝ} (hq : ContinuousAt q 0)
    (hpos : ∀ ε : ℝ, 0 < ε → 0 ≤ q ε) : 0 ≤ q 0 := by
  apply ge_of_tendsto (hq.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto q (𝓝[>] 0) (𝓝 (q 0)))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hpos ε hε

theorem F_common_epsilon {A c d e f : ℝ}
    (hpos : ∀ ε : ℝ, 0 < ε → 0 ≤ F (A+ε) (c+ε) (d+ε) (e+ε) (f+ε)) :
    0 ≤ F A c d e f := by
  have hcont : Continuous (fun ε : ℝ => F (A+ε) (c+ε) (d+ε) (e+ε) (f+ε)) := by
    unfold F phi
    fun_prop
  simpa using nonneg_at_zero_of_pos hcont.continuousAt hpos

/-- Closes the whole ordered cone after a positive-interior proof.
All weak ties are preserved by the same epsilon, including the named faces. -/
theorem F_closed_of_positive
    (h : ∀ A c d e f : ℝ, c ≤ A → d ≤ c → e ≤ d → f ≤ e → 0 < f →
      0 ≤ F A c d e f)
    {A c d e f : ℝ} (hAc : c ≤ A) (hcd : d ≤ c)
    (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ F A c d e f := by
  apply F_common_epsilon
  intro ε hε
  exact h _ _ _ _ _ (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

theorem J_closed_of_positive
    (h : ∀ A D e : ℝ, D ≤ A → e ≤ D → 0 < e → 0 ≤ J A D e)
    {A D e : ℝ} (hAD : D ≤ A) (hDe : e ≤ D) (he : 0 ≤ e) :
    0 ≤ J A D e := by
  have hc : Continuous (fun ε : ℝ => J (A+ε) (D+ε) (e+ε)) := by
    unfold J phi
    fun_prop
  have hh : ∀ ε : ℝ, 0 < ε → 0 ≤ J (A+ε) (D+ε) (e+ε) :=
    fun ε hε => h _ _ _ (by linarith) (by linarith) (by linarith)
  simpa using nonneg_at_zero_of_pos hc.continuousAt hh

theorem G_closed_of_positive
    (h : ∀ A C E : ℝ, C ≤ A → E ≤ C → 0 < E → 0 ≤ G A C E)
    {A C E : ℝ} (hAC : C ≤ A) (hCE : E ≤ C) (hE : 0 ≤ E) :
    0 ≤ G A C E := by
  have hc : Continuous (fun ε : ℝ => G (A+ε) (C+ε) (E+ε)) := by
    unfold G phi
    fun_prop
  have hh : ∀ ε : ℝ, 0 < ε → 0 ≤ G (A+ε) (C+ε) (E+ε) :=
    fun ε hε => h _ _ _ (by linarith) (by linarith) (by linarith)
  simpa using nonneg_at_zero_of_pos hc.continuousAt hh

/-- The D=0 section-3 degeneracy is exact, with no logarithm derivatives. -/
theorem J_zero_zero (A : ℝ) : J A 0 0 = 0 := by
  simp [J, phi]

/-- Affine precomposition of the globally continuous concave entropy. -/
theorem concave_negMulLog_affine {s : Set ℝ} (hs : Convex ℝ s)
    (a b : ℝ) (hpos : ∀ t ∈ s, 0 ≤ a*t+b) :
    ConcaveOn ℝ s (fun t => Real.negMulLog (a*t+b)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy u v hu hv huv
  have hh := Real.concaveOn_negMulLog.2 (hpos x hx) (hpos y hy) hu hv huv
  simp only [smul_eq_mul] at hh ⊢
  have heq : a*(u*x+v*y)+b = u*(a*x+b)+v*(a*y+b) := by
    calc
      _ = a*(u*x+v*y)+(u+v)*b := by rw [huv, one_mul]
      _ = _ := by ring
  rw [heq]
  exact hh

/-- Sum of any finite collection of affine entropy terms, plus a constant,
is concave on a closed interval whenever its arguments stay nonnegative.
Used for the marginal-preserving fibre, including zero marginals. -/
theorem concave_entropy_sum {ι : Type*} [Fintype ι]
    {s : Set ℝ} (hs : Convex ℝ s) (a b : ι → ℝ) (K : ℝ)
    (hp : ∀ i t, t ∈ s → 0 ≤ a i*t+b i) :
    ConcaveOn ℝ s (fun t => K+∑ i, Real.negMulLog (a i*t+b i)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy u v hu hv huv
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (concave_negMulLog_affine hs (a i) (b i) (hp i)).2 hx hy hu hv huv)
  simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hh ⊢
  have hK : u*K+v*K=K := by
    calc
      _ = (u+v)*K := by ring
      _ = K := by rw [huv, one_mul]
  simp only [mul_add] at hh ⊢
  linarith

#print axioms F_closed_of_positive
#print axioms J_closed_of_positive
#print axioms G_closed_of_positive
#print axioms J_zero_zero
#print axioms concave_entropy_sum
end McConnell
```

### `EntropicFibre.lean`

```lean
import EntropicBoundary
import Mathlib.Tactic.FinCases

open Real Set
namespace McConnell

noncomputable def fibreLo (c d e f : ℝ) : ℝ := max ((d-c)/2) ((f-e)/2)
noncomputable def fibreHi (A c d e f : ℝ) : ℝ := min (A-c) (min ((d-e)/2) f)

theorem fibre_contains_zero {A c d e f : ℝ}
    (hAc : c ≤ A) (hcd : d ≤ c) (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    fibreLo c d e f ≤ 0 ∧ 0 ≤ fibreHi A c d e f := by
  unfold fibreLo fibreHi
  constructor
  · apply max_le <;> linarith
  · apply le_min
    · linarith
    · apply le_min <;> linarith

theorem fibre_order {A c d e f t : ℝ}
    (ht : t ∈ Icc (fibreLo c d e f) (fibreHi A c d e f)) :
    c+t ≤ A ∧ d-t ≤ c+t ∧ e+t ≤ d-t ∧ f-t ≤ e+t ∧ 0 ≤ f-t := by
  have hl1 : (d-c)/2 ≤ t := le_trans (le_max_left _ _) ht.1
  have hl2 : (f-e)/2 ≤ t := le_trans (le_max_right _ _) ht.1
  have hu1 : t ≤ A-c := le_trans ht.2 (min_le_left _ _)
  have hu2 : t ≤ (d-e)/2 :=
    le_trans ht.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hu3 : t ≤ f :=
    le_trans ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem F_fibre_identity (A c d e f t : ℝ) :
    F A (c+t) (d-t) (e+t) (f-t) =
      (phi (A+c+f)+phi (A+d+e)+phi (2*A)+phi (c+d)+phi (e+f)-phi (d+e))
      + ∑ i : Fin 4, Real.negMulLog ((![-1,1,-1,1] : Fin 4 → ℝ) i*t+
          (![2*A+d,c+e+f,A+f,A+c] : Fin 4 → ℝ) i) := by
  simp [F, phi, Real.negMulLog, Fin.sum_univ_succ]
  ring

/-- The actual final fibre is concave even when some marginals vanish. -/
theorem F_fibre_concave {A c d e f : ℝ}
    (hAc : c ≤ A) (hcd : d ≤ c) (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    ConcaveOn ℝ (Icc (fibreLo c d e f) (fibreHi A c d e f))
      (fun t => F A (c+t) (d-t) (e+t) (f-t)) := by
  have hc0 : 0 ≤ c := le_trans hf (le_trans hef (le_trans hde hcd))
  have hA0 : 0 ≤ A := le_trans hc0 hAc
  have hh := concave_entropy_sum (ι := Fin 4) (convex_Icc (fibreLo c d e f) (fibreHi A c d e f))
    (![-1,1,-1,1]) (![2*A+d,c+e+f,A+f,A+c])
    (phi (A+c+f)+phi (A+d+e)+phi (2*A)+phi (c+d)+phi (e+f)-phi (d+e))
    (by
      intro i t ht
      have ho := fibre_order ht
      fin_cases i <;> simp
      all_goals linarith [ho.2.2.2.2, ho.2.2.2.1, ho.2.2.1, ho.2.1, ho.1])
  simpa only [← F_fibre_identity] using hh

/-- Interface for completing §7: once the five faces are proved, no further
calculus, differentiability at zero, or approximation is needed. -/
theorem F_nonneg_of_faces
    (hcdFace : ∀ A C e f : ℝ, C ≤ A → e ≤ C → f ≤ e → 0 ≤ f → 0 ≤ F A C C e f)
    (hefFace : ∀ A c d E : ℝ, c ≤ A → d ≤ c → E ≤ d → 0 ≤ E → 0 ≤ F A c d E E)
    (hcAFace : ∀ A d e f : ℝ, d ≤ A → e ≤ d → f ≤ e → 0 ≤ f → 0 ≤ F A A d e f)
    (hdeFace : ∀ A c D f : ℝ, c ≤ A → D ≤ c → f ≤ D → 0 ≤ f → 0 ≤ F A c D D f)
    (hfFace : ∀ A c d e : ℝ, c ≤ A → d ≤ c → e ≤ d → 0 ≤ e → 0 ≤ F A c d e 0)
    {A c d e f : ℝ} (hAc : c ≤ A) (hcd : d ≤ c)
    (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ F A c d e f := by
  let l := fibreLo c d e f
  let u := fibreHi A c d e f
  have h0 := fibre_contains_zero hAc hcd hde hef hf
  have hlu : l ≤ u := le_trans h0.1 h0.2
  have hlI : l ∈ Icc l u := ⟨le_rfl, hlu⟩
  have huI : u ∈ Icc l u := ⟨hlu, le_rfl⟩
  have hoL := fibre_order hlI
  have hoU := fibre_order huI
  have hL : 0 ≤ F A (c+l) (d-l) (e+l) (f-l) := by
    by_cases hh : (f-e)/2 ≤ (d-c)/2
    · have hl : l = (d-c)/2 := max_eq_left hh
      have heq : c+l = d-l := by rw [hl]; ring
      rw [heq]
      exact hcdFace _ _ _ _ (by linarith [hoL.1]) hoL.2.2.1 hoL.2.2.2.1 hoL.2.2.2.2
    · have hl : l = (f-e)/2 := max_eq_right (le_of_lt (lt_of_not_ge hh))
      have heq : e+l = f-l := by rw [hl]; ring
      rw [heq]
      exact hefFace _ _ _ _ hoL.1 hoL.2.1 (by linarith [hoL.2.2.1]) hoL.2.2.2.2
  have hU : 0 ≤ F A (c+u) (d-u) (e+u) (f-u) := by
    by_cases hh : A-c ≤ min ((d-e)/2) f
    · have hu : u = A-c := min_eq_left hh
      have heq : c+u = A := by rw [hu]; ring
      rw [heq]
      exact hcAFace _ _ _ _ (by linarith [hoU.2.1]) hoU.2.2.1 hoU.2.2.2.1 hoU.2.2.2.2
    · have hu : u = min ((d-e)/2) f := min_eq_right (le_of_lt (lt_of_not_ge hh))
      by_cases hdf : (d-e)/2 ≤ f
      · have hu' : u = (d-e)/2 := hu.trans (min_eq_left hdf)
        have heq : d-u = e+u := by rw [hu']; ring
        rw [heq]
        exact hdeFace _ _ _ _ hoU.1 (by linarith [hoU.2.1]) hoU.2.2.2.1 hoU.2.2.2.2
      · have hu' : u = f := hu.trans (min_eq_right (le_of_lt (lt_of_not_ge hdf)))
        have heq : f-u = 0 := by rw [hu']; ring
        rw [heq]
        exact hfFace _ _ _ _ hoU.1 hoU.2.1 hoU.2.2.1 (by linarith [hoU.2.2.2.1, hoU.2.2.2.2])
  have hc := F_fibre_concave hAc hcd hde hef hf
  have hs : (0 : ℝ) ∈ segment ℝ l u := by
    rw [segment_eq_Icc hlu]
    exact h0
  have hh := hc.ge_on_segment hlI huI hs
  have hh0 : 0 ≤ min (F A (c+l) (d-l) (e+l) (f-l)) (F A (c+u) (d-u) (e+u) (f-u)) :=
    le_min hL hU
  simpa using le_trans hh0 hh

#print axioms F_fibre_concave
#print axioms F_nonneg_of_faces
end McConnell
```

### `EntropicGradient.lean`

```lean
import EntropicPath

open Real
namespace McConnell
noncomputable def PA (A C : ℝ) : ℝ := (2*A)^2*(A+C+1)^2
noncomputable def QA (A C : ℝ) : ℝ := (2*A+C)^2*(A+1)*(A+C)
noncomputable def PC (A C : ℝ) : ℝ := (2*C)^2*(A+C+1)^2
noncomputable def QC (A C : ℝ) : ℝ := (2*A+C)*(C+2)*(A+C)*(C+1)
noncomputable def R (A C : ℝ) : ℝ :=
  (A-C)^2*(C-1)*(C+2)+(A-C)*C*(C+1)*(3*C-2)+2*C^3*(C-1)

theorem gA_log_ratio {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    gA A C = log (PA A C / QA A C) := by
  have h2A : 2*A ≠ 0 := by positivity
  have hS : A+C+1 ≠ 0 := by positivity
  have hT : 2*A+C ≠ 0 := by positivity
  have hU : A+1 ≠ 0 := by positivity
  have hV : A+C ≠ 0 := by positivity
  simp [gA, PA, QA, Real.log_div, Real.log_mul, Real.log_pow, h2A, hS, hT, hU, hV]
  ring

theorem gC_log_ratio {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    gC A C = log (PC A C / QC A C) := by
  have h2C : 2*C ≠ 0 := by positivity
  have hS : A+C+1 ≠ 0 := by positivity
  have hT : 2*A+C ≠ 0 := by positivity
  have hU : C+2 ≠ 0 := by positivity
  have hV : A+C ≠ 0 := by positivity
  have hW : C+1 ≠ 0 := by positivity
  simp [gC, PC, QC, Real.log_div, Real.log_mul, Real.log_pow, h2C, hS, hT, hU, hV, hW]
  ring

theorem R_nonneg {A C : ℝ} (hC : 1 ≤ C) (hAC : C ≤ A) : 0 ≤ R A C := by
  unfold R
  have h0 : 0 ≤ C := by linarith
  have h1 : 0 ≤ C-1 := by linarith
  have h2 : 0 ≤ A-C := sub_nonneg.mpr hAC
  have h3 : 0 ≤ 3*C-2 := by linarith
  positivity

theorem gradient_identity {A C : ℝ} (hA : A ≠ 0) (hC : C ≠ 0)
    (hS : A+C+1 ≠ 0) :
    2*A*(1-QA A C/PA A C)+C*(1-QC A C/PC A C) =
      (2*A+C)*R A C/(4*A*C*(A+C+1)^2) := by
  unfold QA PA QC PC R
  field_simp
  ring

/-- The proof-specific logarithmic gradient inequality, not a convexity-only bound. -/
theorem weighted_gradient_nonneg {A C : ℝ} (hC : 1 ≤ C) (hAC : C ≤ A) :
    0 ≤ 2*A*gA A C+C*gC A C := by
  have hC0 : 0 < C := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le hC0 hAC
  have hpA : 0 < PA A C := by unfold PA; positivity
  have hqA : 0 < QA A C := by unfold QA; positivity
  have hpC : 0 < PC A C := by unfold PC; positivity
  have hqC : 0 < QC A C := by unfold QC; positivity
  have ha := Real.one_sub_inv_le_log_of_pos (div_pos hpA hqA)
  have hc := Real.one_sub_inv_le_log_of_pos (div_pos hpC hqC)
  rw [inv_div] at ha hc
  rw [← gA_log_ratio hA0 hC0] at ha
  rw [← gC_log_ratio hA0 hC0] at hc
  have hh := add_le_add (mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2*A))
    (mul_le_mul_of_nonneg_left hc hC0.le)
  rw [gradient_identity hA0.ne' hC0.ne' (by positivity)] at hh
  have hr : 0 ≤ (2*A+C)*R A C/(4*A*C*(A+C+1)^2) :=
    div_nonneg (mul_nonneg (by positivity) (R_nonneg hC hAC)) (by positivity)
  exact le_trans hr hh

#print axioms weighted_gradient_nonneg
end McConnell
```

### `EntropicEdges.lean`

```lean
import EntropicGradient

open Real Set
namespace McConnell

theorem gA_edge_nonneg {A : ℝ} (hA : 1 ≤ A) : 0 ≤ gA A 1 := by
  have hA0 : 0 < A := by linarith
  have hq : 0 < QA A 1 := by unfold QA; positivity
  have heq : PA A 1-QA A 1 = (A-1)*(4*A^2+7*A+1) := by
    unfold PA QA
    ring
  have hp : QA A 1 ≤ PA A 1 := by
    have hprod : 0 ≤ (A-1)*(4*A^2+7*A+1) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  rw [gA_log_ratio hA0 zero_lt_one]
  apply Real.log_nonneg
  exact (one_le_div hq).2 hp

theorem diagonal_gradient_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ gA t t+gC t t := by
  have ht0 : 0 < t := by linarith
  have h2 : 2*t ≠ 0 := by positivity
  have h3 : 3*t ≠ 0 := by positivity
  have hS : 2*t+1 ≠ 0 := by positivity
  have hU : t+2 ≠ 0 := by positivity
  have hV : t+1 ≠ 0 := by positivity
  have hP : 0 ≤ 37*t^3+57*t^2+18*t-4 := by
    nlinarith [pow_nonneg ht0.le 3, sq_nonneg t]
  have hdiff : (2*t+1)^4*(2*t)^2-(3*t)^3*(t+2)*(t+1)^2 =
      t^2*(t-1)*(37*t^3+57*t^2+18*t-4) := by ring
  have hprod : (3*t)^3*(t+2)*(t+1)^2 ≤ (2*t+1)^4*(2*t)^2 := by
    have hh : 0 ≤ t^2*(t-1)*(37*t^3+57*t^2+18*t-4) :=
      mul_nonneg (mul_nonneg (sq_nonneg t) (by linarith)) hP
    linarith
  have hden : 0 < (3*t)^3*(t+2)*(t+1)^2 := by positivity
  have hl := Real.log_nonneg ((one_le_div hden).2 hprod)
  have heq : log ((2*t+1)^4*(2*t)^2/((3*t)^3*(t+2)*(t+1)^2)) =
      gA t t+gC t t := by
    have hsum : t+t=2*t := by ring
    have hsum3 : 2*t+t=3*t := by ring
    simp [gA, gC, hsum, hsum3, Real.log_div, Real.log_mul, Real.log_pow, h2, h3, hS, hU, hV]
    ring
  rwa [heq] at hl

theorem G_one_one_one : G 1 1 1 = 0 := by
  norm_num [G]
  ring

theorem G_edge_nonneg {A : ℝ} (hA : 1 ≤ A) : 0 ≤ G A 1 1 := by
  have hc : Continuous (fun t : ℝ => G t 1 1) := by unfold G phi; fun_prop
  have hd : ∀ t ∈ interior (Icc 1 A),
      HasDerivAt (fun s : ℝ => G s 1 1) (gA t 1) t := by
    intro t ht
    have ht1 : 1 ≤ t := (interior_subset ht).1
    have hh := G_path_hasDerivAt (hasDerivAt_id t) (hasDerivAt_const t 1)
      (by linarith : 0 < t) zero_lt_one
    simpa only [id_eq, one_mul, zero_mul, add_zero] using hh
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (1 : ℝ) A) hc.continuousOn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t ht).deriv]; exact gA_edge_nonneg (interior_subset ht).1)
  have hh := hm ⟨le_rfl, hA⟩ ⟨hA, le_rfl⟩ hA
  change G 1 1 1 ≤ G A 1 1 at hh
  rwa [G_one_one_one] at hh

theorem G_diagonal_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ G C C 1 := by
  have hc : Continuous (fun t : ℝ => G t t 1) := by unfold G phi; fun_prop
  have hd : ∀ t ∈ interior (Icc 1 C),
      HasDerivAt (fun s : ℝ => G s s 1) (gA t t+gC t t) t := by
    intro t ht
    have ht1 : 1 ≤ t := (interior_subset ht).1
    have hh := G_path_hasDerivAt (hasDerivAt_id t) (hasDerivAt_id t)
      (by linarith : 0 < t) (by linarith : 0 < t)
    simpa only [id_eq, one_mul] using hh
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (1 : ℝ) C) hc.continuousOn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t ht).deriv]; exact diagonal_gradient_nonneg (interior_subset ht).1)
  have hh := hm ⟨le_rfl, hC⟩ ⟨hC, le_rfl⟩ hC
  change G 1 1 1 ≤ G C C 1 at hh
  rwa [G_one_one_one] at hh

theorem G_normalized_nonneg {A C : ℝ} (hAC : C ≤ A) (hC : 1 ≤ C) :
    0 ≤ G A C 1 :=
  G_nonneg_of_weighted_edges
    (fun _ _ hc hac => weighted_gradient_nonneg hc hac)
    (fun _ ha => G_edge_nonneg ha) (fun _ hc => G_diagonal_nonneg hc) hAC hC

#print axioms G_normalized_nonneg
end McConnell
```

### `EntropicPair.lean`

```lean
import EntropicEdges
import EntropicBoundary

open Real
namespace McConnell

theorem phi_mul (x y : ℝ) : phi (x*y) = y*phi x+x*phi y := by
  unfold phi
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

theorem G_homogeneous (r A C E : ℝ) :
    G (r*A) (r*C) (r*E) = r*G A C E := by
  unfold G
  have h0 : r*A+r*C+r*E = r*(A+C+E) := by ring
  have h1 : 2*(r*A) = r*(2*A) := by ring
  have h2 : 2*(r*C) = r*(2*C) := by ring
  have h3 : 2*(r*E) = r*(2*E) := by ring
  have h4 : 2*(r*A)+r*C = r*(2*A+C) := by ring
  have h5 : r*C+2*(r*E) = r*(C+2*E) := by ring
  have h6 : r*A+r*E = r*(A+E) := by ring
  have h7 : r*A+r*C = r*(A+C) := by ring
  have h8 : r*C+r*E = r*(C+E) := by ring
  rw [h0, h4, h5, h6, h7, h8, h1, h2, h3]
  simp only [phi_mul]
  ring

theorem G_nonneg {A C E : ℝ} (hAC : C ≤ A) (hCE : E ≤ C) (hE : 0 ≤ E) :
    0 ≤ G A C E := by
  apply G_closed_of_positive _ hAC hCE hE
  intro A C E hAC hCE hE
  have hnorm : 0 ≤ G (A/E) (C/E) 1 :=
    G_normalized_nonneg ((div_le_div_iff_of_pos_right hE).2 hAC) ((one_le_div hE).2 hCE)
  have hh := G_homogeneous E (A/E) (C/E) 1
  have ha : E*(A/E)=A := by field_simp
  have hc : E*(C/E)=C := by field_simp
  rw [ha, hc, mul_one] at hh
  rw [hh]
  exact mul_nonneg hE.le hnorm

theorem F_pair_nonneg {A C E : ℝ} (hAC : C ≤ A) (hCE : E ≤ C) (hE : 0 ≤ E) :
    0 ≤ F A C C E E := by
  rw [F_G]
  exact G_nonneg hAC hCE hE

#print axioms G_nonneg
#print axioms F_pair_nonneg
end McConnell
```

### `EntropicAudit.lean`

```lean
import EntropicPair
import EntropicFibre

#print axioms McConnell.cmi_gap37
#print axioms McConnell.cmi_gap43
#print axioms McConnell.cmi_gap49
#print axioms McConnell.InD6_uniform
#print axioms McConnell.endpoint_iff
#print axioms McConnell.F_zero_last
#print axioms McConnell.F_J
#print axioms McConnell.F_G
#print axioms McConnell.phi_comp_hasDerivAt
#print axioms McConnell.J_path_hasDerivAt
#print axioms McConnell.critical_pos
#print axioms McConnell.critical_identity
#print axioms McConnell.critical_log_identity
#print axioms McConnell.envelope_hasDerivAt
#print axioms McConnell.envelope_derivative_nonneg
#print axioms McConnell.envelope_monotone
#print axioms McConnell.envelope_ge_face
#print axioms McConnell.G_path_hasDerivAt
#print axioms McConnell.path_lower_bound
#print axioms McConnell.path_in_cone
#print axioms McConnell.G_nonneg_of_weighted_edges
#print axioms McConnell.continuous_phi
#print axioms McConnell.nonneg_at_zero_of_pos
#print axioms McConnell.F_common_epsilon
#print axioms McConnell.F_closed_of_positive
#print axioms McConnell.J_closed_of_positive
#print axioms McConnell.G_closed_of_positive
#print axioms McConnell.J_zero_zero
#print axioms McConnell.concave_negMulLog_affine
#print axioms McConnell.concave_entropy_sum
#print axioms McConnell.fibre_contains_zero
#print axioms McConnell.fibre_order
#print axioms McConnell.F_fibre_identity
#print axioms McConnell.F_fibre_concave
#print axioms McConnell.F_nonneg_of_faces
#print axioms McConnell.gA_log_ratio
#print axioms McConnell.gC_log_ratio
#print axioms McConnell.R_nonneg
#print axioms McConnell.gradient_identity
#print axioms McConnell.weighted_gradient_nonneg
#print axioms McConnell.gA_edge_nonneg
#print axioms McConnell.diagonal_gradient_nonneg
#print axioms McConnell.G_one_one_one
#print axioms McConnell.G_edge_nonneg
#print axioms McConnell.G_diagonal_nonneg
#print axioms McConnell.G_normalized_nonneg
#print axioms McConnell.phi_mul
#print axioms McConnell.G_homogeneous
#print axioms McConnell.G_nonneg
#print axioms McConnell.F_pair_nonneg
```

### `EntropicReductions.lean`

```lean
import EntropicPair
import EntropicFibre

open Real Set
set_option linter.unnecessarySeqFocus false
namespace McConnell

/-- Product comparisons supply the signs of the four logarithms. -/
theorem logs_nonpos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h : a*b ≤ c*d) :
    log a+log b-log c-log d ≤ 0 := by
  have hh := Real.log_le_log (mul_pos ha hb) h
  rw [Real.log_mul ha.ne' hb.ne', Real.log_mul hc.ne' hd.ne'] at hh
  linarith

theorem logs_nonneg {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h : c*d ≤ a*b) :
    0 ≤ log a+log b-log c-log d := by
  have hh := logs_nonpos hc hd ha hb h
  linarith

theorem compare_increasing {q : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hc : ContinuousOn q (Icc l u))
    (hd : ∀ t ∈ Ioo l u, ∃ v, HasDerivAt q v t ∧ 0 ≤ v) : q l ≤ q u := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc l u) hc ?_ ?_
    ⟨le_rfl, hlu⟩ ⟨hlu, le_rfl⟩ hlu
  · intro t ht
    obtain ⟨v, hv, _⟩ := hd t (by simpa only [interior_Icc] using ht)
    exact hv.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨v, hv, hv0⟩ := hd t (by simpa only [interior_Icc] using ht)
    rwa [hv.deriv]

theorem compare_decreasing {q : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hc : ContinuousOn q (Icc l u))
    (hd : ∀ t ∈ Ioo l u, ∃ v, HasDerivAt q v t ∧ v ≤ 0) : q u ≤ q l := by
  have hh := compare_increasing (q := fun t => -q t) hlu hc.neg (by
    intro t ht
    obtain ⟨v, hv, hv0⟩ := hd t ht
    exact ⟨-v, hv.neg, neg_nonneg.mpr hv0⟩)
  linarith

theorem F_de_c_deriv {A c D f : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hD : 0 < D) (hf : 0 < f) :
    HasDerivAt (fun t => F A t D D f)
      (log (A+c+f)+log (c+D)-log (c+D+f)-log (A+c)) c := by
  have hi := hasDerivAt_id c
  have h1 := phi_comp_hasDerivAt (((hasDerivAt_const c A).add hi).add_const f) (by positivity : 0 < A+c+f)
  have h2 := phi_comp_hasDerivAt (hi.add_const D) (by positivity : 0 < c+D)
  have h3 := phi_comp_hasDerivAt ((hi.add_const D).add_const f) (by positivity : 0 < c+D+f)
  have h4 := phi_comp_hasDerivAt ((hasDerivAt_const c A).add hi) (by positivity : 0 < A+c)
  have hh := ((((((((h1.add_const (phi (A+D+D))).add_const (phi (2*A))).add h2).add_const
    (phi (D+f))).sub_const (phi (2*A+D))).sub h3).sub_const (phi (A+f))).sub h4).sub_const (phi (D+D))
  convert hh using 1 <;> dsimp [F] <;> ring

theorem F_de_f_deriv {A D f : ℝ} (hA : 0 < A) (hD : 0 < D) (hf : 0 < f) :
    HasDerivAt (fun t => F A A D D t)
      (log (2*A+f)+log (D+f)-log (A+D+f)-log (A+f)) f := by
  have hi := hasDerivAt_id f
  have h1 := phi_comp_hasDerivAt ((hasDerivAt_const f (A+A)).add hi) (by positivity : 0 < A+A+f)
  have h2 := phi_comp_hasDerivAt ((hasDerivAt_const f D).add hi) (by positivity : 0 < D+f)
  have h3 := phi_comp_hasDerivAt ((hasDerivAt_const f (A+D)).add hi) (by positivity : 0 < A+D+f)
  have h4 := phi_comp_hasDerivAt ((hasDerivAt_const f A).add hi) (by positivity : 0 < A+f)
  have hh := ((((((((h1.add_const (phi (A+D+D))).add_const (phi (2*A))).add_const
    (phi (A+D))).add h2).sub_const (phi (2*A+D))).sub h3).sub h4).sub_const (phi (A+A))).sub_const (phi (D+D))
  convert hh using 1 <;> dsimp [F] <;> ring_nf

theorem F_de_nonneg {A c D f : ℝ}
    (hAc : c ≤ A) (hDc : D ≤ c) (hfD : f ≤ D) (hf : 0 ≤ f) :
    0 ≤ F A c D D f := by
  apply F_common_epsilon
  intro ε hε
  suffices hs : ∀ A c D f : ℝ, c ≤ A → D ≤ c → f ≤ D → 0 < f → 0 ≤ F A c D D f by
    exact hs _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  intro A c D f hAc hDc hfD hf
  have hD : 0 < D := lt_of_lt_of_le hf hfD
  have hc : 0 < c := lt_of_lt_of_le hD hDc
  have hA : 0 < A := lt_of_lt_of_le hc hAc
  have h1 : F A A D D f ≤ F A c D D f := by
    apply compare_decreasing (q := fun t => F A t D D f) hAc (by unfold F phi; fun_prop)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨_, F_de_c_deriv hA (by linarith) hD hf, ?_⟩
    apply logs_nonpos <;> try positivity
    nlinarith [mul_nonneg hf.le (sub_nonneg.mpr (le_trans hDc hAc))]
  have h2 : F A A D D D ≤ F A A D D f := by
    apply compare_decreasing (q := fun t => F A A D D t) hfD (by unfold F phi; fun_prop)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨_, F_de_f_deriv hA hD (by linarith), ?_⟩
    apply logs_nonpos <;> try positivity
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr (le_trans hDc hAc))]
  have hz : F A A D D D = 0 := by
    unfold F
    ring_nf
  linarith

#print axioms F_de_nonneg
end McConnell
```

### `EntropicZero.lean`

```lean
import EntropicReductions

open Real Set
set_option linter.unnecessarySeqFocus false
namespace McConnell

theorem J_e_deriv {A D e : ℝ} (hA : 0 < A) (hD : 0 < D) (he : 0 < e) :
    HasDerivAt (J A D)
      (log (A+D+e)+log e-log (D+e)-log (D+e)) e := by
  have hi := hasDerivAt_id e
  have h1 := phi_comp_hasDerivAt ((hasDerivAt_const e (A+D)).add hi) (by positivity : 0 < A+D+e)
  have h2 := phi_comp_hasDerivAt hi he
  have h3 := phi_comp_hasDerivAt ((hasDerivAt_const e D).add hi) (by positivity : 0 < D+e)
  have hh := ((((((h1.add_const (phi (2*A))).add_const (phi (2*D))).add h2).sub_const
    (phi (2*A+D))).sub h3).sub_const (phi A)).sub h3
  convert hh using 1
  · rfl
  · dsimp; ring

theorem J_nonneg {A D e : ℝ}
    (hAD : D ≤ A) (hDe : e ≤ D) (he : 0 ≤ e) : 0 ≤ J A D e := by
  apply J_closed_of_positive ?_ hAD hDe he
  intro A D e hAD hDe he
  have hD : 0 < D := lt_of_lt_of_le he hDe
  have hA : 0 < A := lt_of_lt_of_le hD hAD
  have hface : 0 ≤ J A D D := by
    rw [← F_J]
    exact F_de_nonneg hAD le_rfl (by positivity) (by norm_num)
  by_cases hsmall : A ≤ 2*D
  · have hmono : J A D D ≤ J A D e := by
      apply compare_decreasing (q := J A D) hDe (by unfold J phi; fun_prop)
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      refine ⟨_, J_e_deriv hA hD (by linarith [ht.1]), ?_⟩
      apply logs_nonpos <;> try positivity
      have hprod : t*(A-D) ≤ D*D :=
        le_trans (mul_le_mul_of_nonneg_right ht.2.le (by linarith))
          (mul_le_mul_of_nonneg_left (by linarith : A-D ≤ D) hD.le)
      nlinarith
    linarith
  · have hAD' : D < A := by linarith
    have hcrit := critical_pos hD hAD'
    have hden : 0 < A-D := by linarith
    have hcritD : critical A D ≤ D := by
      unfold critical
      apply (div_le_iff₀ hden).2
      nlinarith
    have henv : 0 ≤ J A D (critical A D) :=
      le_trans (by
        rw [← F_J]
        exact F_de_nonneg (by linarith) le_rfl (by positivity) (by norm_num))
        (envelope_ge_face hD (by linarith))
    have hprod : critical A D*(A-D) = D^2 := by
      unfold critical
      field_simp [hden.ne']
    by_cases hecrit : e ≤ critical A D
    · have hm : J A D (critical A D) ≤ J A D e := by
        apply compare_decreasing (q := J A D) hecrit (by unfold J phi; fun_prop)
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        refine ⟨_, J_e_deriv hA hD (by linarith [ht.1]), ?_⟩
        apply logs_nonpos <;> try positivity
        nlinarith [mul_le_mul_of_nonneg_right ht.2.le hden.le]
      linarith
    · have hce : critical A D ≤ e := le_of_lt (lt_of_not_ge hecrit)
      have hm : J A D (critical A D) ≤ J A D e := by
        apply compare_increasing (q := J A D) hce (by unfold J phi; fun_prop)
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        refine ⟨_, J_e_deriv hA hD (by linarith [ht.1]), ?_⟩
        apply logs_nonneg <;> try positivity
        nlinarith [mul_le_mul_of_nonneg_right ht.1.le hden.le]
      linarith

theorem F_f0_c_deriv {A c d e : ℝ} (_hA : 0 < A) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    HasDerivAt (fun t => F A t d e 0) (log (c+d)-log (c+e)) c := by
  have hi := hasDerivAt_id c
  have h1 := phi_comp_hasDerivAt (hi.add_const d) (by positivity : 0 < c+d)
  have h2 := phi_comp_hasDerivAt (hi.add_const e) (by positivity : 0 < c+e)
  have hh := ((((((hasDerivAt_const c (phi (A+d+e))).add_const (phi (2*A))).add h1).add_const
    (phi e)).sub_const (phi (2*A+d))).sub h2).sub_const (phi A) |>.sub_const (phi (d+e))
  simp_rw [F_zero_last]
  convert hh using 1 <;> dsimp <;> ring

theorem F_f0_nonneg {A c d e : ℝ}
    (hAc : c ≤ A) (hcd : d ≤ c) (hde : e ≤ d) (he : 0 ≤ e) :
    0 ≤ F A c d e 0 := by
  have hc : Continuous (fun ε : ℝ => F (A+ε) (c+ε) (d+ε) (e+ε) 0) := by
    unfold F phi
    fun_prop
  suffices hs : ∀ A c d e : ℝ, c ≤ A → d ≤ c → e ≤ d → 0 < e → 0 ≤ F A c d e 0 by
    have hh := nonneg_at_zero_of_pos hc.continuousAt (fun ε hε =>
      hs _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith))
    simpa using hh
  intro A c d e hAc hcd hde he
  have hd : 0 < d := lt_of_lt_of_le he hde
  have hA : 0 < A := lt_of_lt_of_le hd (le_trans hcd hAc)
  have hm : F A d d e 0 ≤ F A c d e 0 := by
    apply compare_increasing (q := fun t => F A t d e 0) hcd (by unfold F phi; fun_prop)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨_, F_f0_c_deriv hA (by linarith) hd he, ?_⟩
    have hh := Real.log_le_log (by linarith [ht.1] : 0 < t+e) (by linarith : t+e ≤ t+d)
    linarith
  rw [F_J] at hm
  exact le_trans (J_nonneg (le_trans hcd hAc) hde he.le) hm

#print axioms J_nonneg
#print axioms F_f0_nonneg
end McConnell
```

### `EntropicIncrement.lean`

```lean
import EntropicBoundary
import Mathlib.Analysis.Convex.Deriv

open Real Set
namespace McConnell
set_option linter.unnecessarySeqFocus false

noncomputable def increment (h x : ℝ) : ℝ := phi (x+h)-phi x

theorem increment_concave {h : ℝ} (hh : 0 ≤ h) :
    ConcaveOn ℝ (Ici 0) (increment h) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x => log (x+h)-log x)
    (f'' := fun x => (x+h)⁻¹-x⁻¹) (convex_Ici 0)
    (by unfold increment phi; fun_prop)
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have h1 := phi_comp_hasDerivAt ((hasDerivAt_id x).add_const h) (by linarith : 0 < x+h)
    have h2 := phi_comp_hasDerivAt (hasDerivAt_id x) hx0
    have hd : HasDerivAt (increment h) (log (x+h)-log x) x := by
      change HasDerivAt (fun t => phi (t+h)-phi t) (log (x+h)-log x) x
      convert h1.sub h2 using 1
      · rfl
      · simp only [id_eq, mul_one]; ring
    exact hd.hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hd := (((hasDerivAt_id x).add_const h).log (by linarith : x+h ≠ 0)).sub
      ((hasDerivAt_id x).log hx0.ne')
    convert hd.hasDerivWithinAt using 1
    · rfl
    · simp only [id_eq, one_div]
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hi := one_div_le_one_div_of_le hx0 (by linarith : x ≤ x+h)
    simpa only [one_div, sub_nonpos] using hi

theorem concave_affine_nonneg {q : ℝ → ℝ} (hq : ConcaveOn ℝ (Ici 0) q)
    {s : Set ℝ} (hs : Convex ℝ s) (a b : ℝ)
    (hp : ∀ t ∈ s, 0 ≤ a*t+b) : ConcaveOn ℝ s (fun t => q (a*t+b)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy u v hu hv huv
  have hh := hq.2 (hp x hx) (hp y hy) hu hv huv
  simp only [smul_eq_mul] at hh ⊢
  have heq : a*(u*x+v*y)+b = u*(a*x+b)+v*(a*y+b) := by
    calc
      _ = a*(u*x+v*y)+(u+v)*b := by rw [huv, one_mul]
      _ = _ := by ring
  rw [heq]
  exact hh

theorem concave_increment_affine {s : Set ℝ} (hs : Convex ℝ s)
    {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) (hp : ∀ t ∈ s, 0 ≤ a*t+b) :
    ConcaveOn ℝ s (fun t => increment h (a*t+b)) :=
  concave_affine_nonneg (increment_concave hh) hs a b hp

theorem concave_endpoint_nonneg {q : ℝ → ℝ} {l u t : ℝ}
    (hq : ConcaveOn ℝ (Icc l u) q) (ht : t ∈ Icc l u)
    (hl : 0 ≤ q l) (hu : 0 ≤ q u) : 0 ≤ q t := by
  have hlu : l ≤ u := le_trans ht.1 ht.2
  have hs : t ∈ segment ℝ l u := by rwa [segment_eq_Icc hlu]
  exact le_trans (le_min hl hu) (hq.ge_on_segment ⟨le_rfl,hlu⟩ ⟨hlu,le_rfl⟩ hs)

#print axioms increment_concave
end McConnell
```

### `EntropicCD.lean`

```lean
import EntropicZero
import EntropicIncrement

open Real Set
namespace McConnell
set_option linter.unnecessarySeqFocus false

theorem F_cd_concave {A C e f : ℝ}
    (hAC : C ≤ A) (heC : e ≤ C) (hfe : f ≤ e) (hf : 0 ≤ f) :
    ConcaveOn ℝ (Icc ((f-e)/2) (min (C-e) f))
      (fun t => F A C C (e+t) (f-t)) := by
  let s := Icc ((f-e)/2) (min (C-e) f)
  have hC : 0 ≤ C := by linarith
  have hA : 0 ≤ A := by linarith
  have ho : ∀ t ∈ s, 0 ≤ f-t ∧ f-t ≤ e+t ∧ e+t ≤ C := by
    intro t ht
    have h1 := ht.1
    have h2 := le_trans ht.2 (min_le_left (C-e) f)
    have h3 := le_trans ht.2 (min_le_right (C-e) f)
    exact ⟨by linarith, by linarith, by linarith⟩
  have h1 := concave_increment_affine (convex_Icc _ _) hC (-1) (A+f) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.1])
  have h2 := concave_increment_affine (convex_Icc _ _) hA 1 (C+e) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.1, hh.2.1])
  have hh := (h1.add h2).add (concaveOn_const (c := phi (2*A)+phi (2*C)+phi (e+f)-
    phi (2*A+C)-phi (C+e+f)-phi (A+C)) (convex_Icc ((f-e)/2) (min (C-e) f)))
  convert hh using 1
  ext t
  simp only [increment, Pi.add_apply]
  unfold F
  ring_nf

theorem F_cd_nonneg {A C e f : ℝ}
    (hAC : C ≤ A) (heC : e ≤ C) (hfe : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ F A C C e f := by
  let l := (f-e)/2
  let u := min (C-e) f
  have hl0 : l ≤ 0 := by dsimp [l]; linarith
  have hu0 : 0 ≤ u := le_min (by linarith) hf
  have ho : ∀ t ∈ Icc l u, e+t ≤ C ∧ f-t ≤ e+t ∧ 0 ≤ f-t := by
    intro t ht
    have h1 := ht.1
    have h2 := le_trans ht.2 (min_le_left (C-e) f)
    have h3 := le_trans ht.2 (min_le_right (C-e) f)
    dsimp [l] at h1
    exact ⟨by linarith, by linarith, by linarith⟩
  have hlI : l ∈ Icc l u := ⟨le_rfl, le_trans hl0 hu0⟩
  have huI : u ∈ Icc l u := ⟨le_trans hl0 hu0, le_rfl⟩
  have hlo := ho l hlI
  have huo := ho u huI
  have hL : 0 ≤ F A C C (e+l) (f-l) := by
    have heq : e+l = f-l := by dsimp [l]; ring
    rw [heq]
    exact F_pair_nonneg hAC (by linarith [hlo.1]) hlo.2.2
  have hU : 0 ≤ F A C C (e+u) (f-u) := by
    by_cases hh : C-e ≤ f
    · have hu : u = C-e := min_eq_left hh
      have heq : e+u = C := by rw [hu]; ring
      rw [heq]
      exact F_de_nonneg hAC le_rfl (by linarith [huo.2.1]) huo.2.2
    · have hu : u = f := min_eq_right (le_of_lt (lt_of_not_ge hh))
      have heq : f-u = 0 := by rw [hu]; ring
      rw [heq]
      exact F_f0_nonneg hAC le_rfl huo.1 (by linarith [huo.2.1, huo.2.2])
  have hh := concave_endpoint_nonneg (F_cd_concave hAC heC hfe hf) ⟨hl0,hu0⟩ hL hU
  simpa using hh

#print axioms F_cd_nonneg
end McConnell
```

### `EntropicFaces.lean`

```lean
import EntropicCD

open Real Set
namespace McConnell
set_option linter.unnecessarySeqFocus false

theorem F_cA_d_deriv {A d e f : ℝ} (hA : 0 < A) (hd : 0 < d)
    (he : 0 < e) : HasDerivAt (fun t => F A A t e f)
      (log (A+d+e)+log (A+d)-log (2*A+d)-log (d+e)) d := by
  have hi := hasDerivAt_id d
  have h1 := phi_comp_hasDerivAt (((hasDerivAt_const d A).add hi).add_const e) (by positivity : 0 < A+d+e)
  have h2 := phi_comp_hasDerivAt ((hasDerivAt_const d A).add hi) (by positivity : 0 < A+d)
  have h3 := phi_comp_hasDerivAt ((hasDerivAt_const d (2*A)).add hi) (by positivity : 0 < 2*A+d)
  have h4 := phi_comp_hasDerivAt (hi.add_const e) (by positivity : 0 < d+e)
  have hh := ((((((((hasDerivAt_const d (phi (A+A+f))).add h1).add_const (phi (2*A))).add h2).add_const
    (phi (e+f))).sub h3).sub_const (phi (A+e+f))).sub_const (phi (A+f))).sub_const (phi (A+A)) |>.sub h4
  convert hh using 1
  · rfl
  · dsimp; ring

theorem F_cA_nonneg {A d e f : ℝ}
    (hdA : d ≤ A) (hed : e ≤ d) (hfe : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ F A A d e f := by
  apply F_common_epsilon
  intro ε hε
  suffices hs : ∀ A d e f : ℝ, d ≤ A → e ≤ d → f ≤ e → 0 < f → 0 ≤ F A A d e f by
    exact hs _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  intro A d e f hdA hed hfe hf
  have he : 0 < e := lt_of_lt_of_le hf hfe
  have hA : 0 < A := lt_of_lt_of_le he (le_trans hed hdA)
  have hm : F A A e e f ≤ F A A d e f := by
    apply compare_increasing (q := fun t => F A A t e f) hed (by unfold F phi; fun_prop)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨_, F_cA_d_deriv hA ht0 he, ?_⟩
    apply logs_nonneg <;> try positivity
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr (le_trans hed hdA))]
  exact le_trans (F_de_nonneg le_rfl (le_trans hed hdA) hfe hf.le) hm

theorem F_ef_concave {A c d E : ℝ}
    (hcA : c ≤ A) (hdc : d ≤ c) (hEd : E ≤ d) (hE : 0 ≤ E) :
    ConcaveOn ℝ (Icc ((d-c)/2) (min (A-c) (d-E)))
      (fun t => F A (c+t) (d-t) E E) := by
  let s := Icc ((d-c)/2) (min (A-c) (d-E))
  have hA : 0 ≤ A := by linarith
  have ho : ∀ t ∈ s, c+t ≤ A ∧ d-t ≤ c+t ∧ E ≤ d-t := by
    intro t ht
    have h1 := ht.1
    have h2 := le_trans ht.2 (min_le_left (A-c) (d-E))
    have h3 := le_trans ht.2 (min_le_right (A-c) (d-E))
    exact ⟨by linarith, by linarith, by linarith⟩
  have h1 := concave_increment_affine (convex_Icc _ _) hE 1 (A+c) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.2.1, hh.2.2])
  have h2 := concave_increment_affine (convex_Icc _ _) hA (-1) (d+E) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.2.2])
  have h3 := concave_negMulLog_affine (convex_Icc _ _) (-1) (2*A+d) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.2.2])
  have h4 := concave_negMulLog_affine (convex_Icc _ _) 1 (c+2*E) (by
    intro t ht
    have hh := ho t ht
    linarith [hh.2.1, hh.2.2])
  have hh := (((h1.add h2).add h3).add h4).add
    (concaveOn_const (c := phi (2*A)+phi (c+d)+phi (2*E)-phi (A+E))
      (convex_Icc ((d-c)/2) (min (A-c) (d-E))))
  convert hh using 1
  ext t
  simp only [increment, Pi.add_apply, Real.negMulLog]
  unfold F phi
  ring

theorem F_ef_nonneg {A c d E : ℝ}
    (hcA : c ≤ A) (hdc : d ≤ c) (hEd : E ≤ d) (hE : 0 ≤ E) :
    0 ≤ F A c d E E := by
  let l := (d-c)/2
  let u := min (A-c) (d-E)
  have hl0 : l ≤ 0 := by dsimp [l]; linarith
  have hu0 : 0 ≤ u := le_min (by linarith) (by linarith)
  have ho : ∀ t ∈ Icc l u, c+t ≤ A ∧ d-t ≤ c+t ∧ E ≤ d-t := by
    intro t ht
    have h1 := ht.1
    have h2 := le_trans ht.2 (min_le_left (A-c) (d-E))
    have h3 := le_trans ht.2 (min_le_right (A-c) (d-E))
    dsimp [l] at h1
    exact ⟨by linarith, by linarith, by linarith⟩
  have hlo := ho l ⟨le_rfl,le_trans hl0 hu0⟩
  have huo := ho u ⟨le_trans hl0 hu0,le_rfl⟩
  have hL : 0 ≤ F A (c+l) (d-l) E E := by
    have heq : c+l = d-l := by dsimp [l]; ring
    rw [heq]
    exact F_pair_nonneg (by linarith [hlo.1]) hlo.2.2 hE
  have hU : 0 ≤ F A (c+u) (d-u) E E := by
    by_cases hh : A-c ≤ d-E
    · have hu : u = A-c := min_eq_left hh
      have heq : c+u = A := by rw [hu]; ring
      rw [heq]
      exact F_cA_nonneg (by linarith [huo.1, huo.2.1]) huo.2.2 le_rfl hE
    · have hu : u = d-E := min_eq_right (le_of_lt (lt_of_not_ge hh))
      have heq : d-u = E := by rw [hu]; ring
      rw [heq]
      exact F_de_nonneg huo.1 (by linarith [huo.2.1, huo.2.2]) le_rfl hE
  have hh := concave_endpoint_nonneg (F_ef_concave hcA hdc hEd hE) ⟨hl0,hu0⟩ hL hU
  simpa using hh

theorem F_nonneg {A c d e f : ℝ}
    (hAc : c ≤ A) (hcd : d ≤ c) (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ F A c d e f :=
  F_nonneg_of_faces (fun _ _ _ _ => F_cd_nonneg) (fun _ _ _ _ => F_ef_nonneg)
    (fun _ _ _ _ => F_cA_nonneg) (fun _ _ _ _ => F_de_nonneg)
    (fun _ _ _ _ => F_f0_nonneg) hAc hcd hde hef hf

#print axioms F_cA_nonneg
#print axioms F_ef_nonneg
#print axioms F_nonneg
end McConnell
```

### `EntropicLargest.lean`

```lean
import EntropicReductions

open Real Set
namespace McConnell
set_option linter.unnecessarySeqFocus false

noncomputable def largest (a b u d f : ℝ) : ℝ :=
  phi (a+u)+phi (a+b)-phi (a+b+d)-phi (a+f)

theorem largest_deriv {a b u d f : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hd : 0 ≤ d) (hf : 0 < f) :
    HasDerivAt (fun t => largest t b u d f)
      (log (a+u)+log (a+b)-log (a+b+d)-log (a+f)) a := by
  have hi := hasDerivAt_id a
  have h1 := phi_comp_hasDerivAt (hi.add_const u) (by positivity : 0 < a+u)
  have h2 := phi_comp_hasDerivAt (hi.add_const b) (by positivity : 0 < a+b)
  have h3 := phi_comp_hasDerivAt ((hi.add_const b).add_const d) (by positivity : 0 < a+b+d)
  have h4 := phi_comp_hasDerivAt (hi.add_const f) (by positivity : 0 < a+f)
  convert ((h1.add h2).sub h3).sub h4 using 1
  · rfl
  · dsimp; ring

theorem largest_reduction {a b u d f : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hbf : f ≤ b) (hf : 0 < f)
    (hd : 0 ≤ d) (hu : d+f ≤ u) :
    largest b b u d f ≤ largest a b u d f := by
  apply compare_increasing (q := fun t => largest t b u d f) hab
    (by unfold largest phi; fun_prop)
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hu0 : 0 < u := by linarith
  refine ⟨_, largest_deriv ht0 hb hu0 hd hf, ?_⟩
  apply logs_nonneg <;> try positivity
  nlinarith [mul_nonneg (by positivity : 0 ≤ t+b) (sub_nonneg.mpr hu),
    mul_nonneg hd (sub_nonneg.mpr hbf)]

theorem row_spread {A c d e f : ℝ}
    (hA : 0 < A) (hd : 0 ≤ d) (hcd : d ≤ c) (hf : 0 < f) (hfe : f ≤ e) :
    phi (A+c+f)+phi (A+d+e) ≤ phi (A+d+f)+phi (A+c+e) := by
  have hm : phi (A+c+f)-phi (A+d+f) ≤ phi (A+c+e)-phi (A+d+e) := by
    apply compare_increasing (q := fun t => phi (A+c+t)-phi (A+d+t)) hfe
      (by unfold phi; fun_prop)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hc : 0 ≤ c := le_trans hd hcd
    have h1 := phi_comp_hasDerivAt ((hasDerivAt_const t (A+c)).add (hasDerivAt_id t))
      (by positivity : 0 < A+c+t)
    have h2 := phi_comp_hasDerivAt ((hasDerivAt_const t (A+d)).add (hasDerivAt_id t))
      (by positivity : 0 < A+d+t)
    refine ⟨log (A+c+t)-log (A+d+t), ?_, ?_⟩
    · convert h1.sub h2 using 1
      · rfl
      · dsimp; ring
    · have hh := Real.log_le_log (by positivity : 0 < A+d+t)
        (by linarith : A+d+t ≤ A+c+t)
      linarith
  linarith

#print axioms largest_reduction
#print axioms row_spread
end McConnell
```

### `EntropicEndpoint.lean`

```lean
import EntropicFaces
import EntropicLargest

open Real Set
namespace McConnell
set_option linter.unnecessarySeqFocus false

theorem three_scalar_positive {a b c d e f : ℝ}
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (hde : e ≤ d) (hef : f ≤ e) (hf : 0 < f) :
    0 ≤ marginalPhi a c f b d e - marginalPhi a b d f c e ∧
    0 ≤ marginalPhi a d e b c f - marginalPhi a b d f c e ∧
    0 ≤ marginalPhi a d f b c e - marginalPhi a b d f c e := by
  have hd : 0 ≤ d := by linarith
  have hb : 0 < b := by linarith
  have hbf : f ≤ b := by linarith
  have h37 := largest_reduction (u := c+f) hab hb hbf hf hd (by linarith)
  have h43 := largest_reduction (u := d+e) hab hb hbf hf hd (by linarith)
  have h49 := largest_reduction (u := d+f) hab hb hbf hf hd le_rfl
  have hF := F_nonneg hbc hcd hde hef hf.le
  have hs := row_spread hb hd hcd hf hef
  unfold largest at h37 h43 h49
  unfold F at hF
  unfold marginalPhi
  ring_nf at h37 h43 h49 hF hs ⊢
  exact ⟨by linarith, by linarith, by linarith⟩

theorem three_scalar_nonneg {a b c d e f : ℝ}
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (hde : e ≤ d) (hef : f ≤ e) (hf : 0 ≤ f) :
    0 ≤ marginalPhi a c f b d e - marginalPhi a b d f c e ∧
    0 ≤ marginalPhi a d e b c f - marginalPhi a b d f c e ∧
    0 ≤ marginalPhi a d f b c e - marginalPhi a b d f c e := by
  have hh := fun ε (hε : 0 < ε) =>
    three_scalar_positive (a := a+ε) (b := b+ε) (c := c+ε) (d := d+ε)
      (e := e+ε) (f := f+ε) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  have h37 : Continuous (fun ε : ℝ => marginalPhi (a+ε) (c+ε) (f+ε) (b+ε) (d+ε) (e+ε) -
      marginalPhi (a+ε) (b+ε) (d+ε) (f+ε) (c+ε) (e+ε)) := by
    unfold marginalPhi phi
    fun_prop
  have h43 : Continuous (fun ε : ℝ => marginalPhi (a+ε) (d+ε) (e+ε) (b+ε) (c+ε) (f+ε) -
      marginalPhi (a+ε) (b+ε) (d+ε) (f+ε) (c+ε) (e+ε)) := by
    unfold marginalPhi phi
    fun_prop
  have h49 : Continuous (fun ε : ℝ => marginalPhi (a+ε) (d+ε) (f+ε) (b+ε) (c+ε) (e+ε) -
      marginalPhi (a+ε) (b+ε) (d+ε) (f+ε) (c+ε) (e+ε)) := by
    unfold marginalPhi phi
    fun_prop
  exact ⟨by simpa using nonneg_at_zero_of_pos h37.continuousAt (fun ε hε => (hh ε hε).1),
    by simpa using nonneg_at_zero_of_pos h43.continuousAt (fun ε hε => (hh ε hε).2.1),
    by simpa using nonneg_at_zero_of_pos h49.continuousAt (fun ε hε => (hh ε hε).2.2)⟩

theorem three_gaps_nonneg (p : Fin 6 → ℝ) (hp : InD6 p) :
    0 ≤ gap37 p ∧ 0 ≤ gap43 p ∧ 0 ≤ gap49 p := by
  exact three_scalar_nonneg (hp.1 0 1 (by decide)) (hp.1 1 2 (by decide))
    (hp.1 2 3 (by decide)) (hp.1 3 4 (by decide)) (hp.1 4 5 (by decide)) hp.2.1

/-- Source Definition 4's convention paragraph: all three sporadic arrays
have mutual information at most that of array 11, on the closed D6. -/
theorem mcconnell_conj19 (p : Fin 6 → ℝ) (hp : InD6 p) :
    cmi (M37 p) ≤ cmi (M11 p) ∧ cmi (M43 p) ≤ cmi (M11 p) ∧ cmi (M49 p) ≤ cmi (M11 p) :=
  (endpoint_iff p).2 (three_gaps_nonneg p hp)

#print mcconnell_conj19
#print axioms three_scalar_positive
#print axioms three_scalar_nonneg
#print axioms three_gaps_nonneg
#print axioms mcconnell_conj19
end McConnell
```

### `EntropicFinalAudit.lean`

```lean
import EntropicEndpoint
import EntropicAudit

namespace McConnell
#print axioms logs_nonpos
#print axioms logs_nonneg
#print axioms compare_increasing
#print axioms compare_decreasing
#print axioms F_de_c_deriv
#print axioms F_de_f_deriv
#print axioms F_de_nonneg
#print axioms J_e_deriv
#print axioms J_nonneg
#print axioms F_f0_c_deriv
#print axioms F_f0_nonneg
#print axioms increment_concave
#print axioms concave_affine_nonneg
#print axioms concave_increment_affine
#print axioms concave_endpoint_nonneg
#print axioms F_cd_concave
#print axioms F_cd_nonneg
#print axioms F_cA_d_deriv
#print axioms F_cA_nonneg
#print axioms F_ef_concave
#print axioms F_ef_nonneg
#print axioms F_nonneg
#print axioms largest_deriv
#print axioms largest_reduction
#print axioms row_spread
#print axioms three_scalar_positive
#print axioms three_scalar_nonneg
#print axioms three_gaps_nonneg
#print axioms mcconnell_conj19
end McConnell
```


import KineticSupport

namespace IndependentAudit
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Explicit raw formulas force the expected statement, rather than merely
-- accepting whatever type an imported theorem happens to have.
theorem momentum_raw (v w n : E) :
    (v - inner ℝ (v-w) n • n) + (w + inner ℝ (v-w) n • n) = v+w := by
  exact KineticSupport.collision_momentum v w n

theorem energy_raw (v w n : E) (unit : inner ℝ n n = 1) :
    ‖v - inner ℝ (v-w) n • n‖^2 + ‖w + inner ℝ (v-w) n • n‖^2
      = ‖v‖^2 + ‖w‖^2 := by
  exact KineticSupport.collision_energy v w n unit

theorem affine_raw (a v : E) (t theta : ℝ) :
    a - theta • v + t • v = a + (t-theta) • v :=
  KineticSupport.affine_time_shift a v t theta

theorem relative_raw (a b v w : E) (theta : ℝ) :
    (b-theta • w)-(a-theta • v) = (b-a)-theta • (w-v) :=
  KineticSupport.relative_origin_shift a b v w theta

theorem contact_raw (a b v w : E) (t theta : ℝ) :
    (a-theta • v+(t+theta) • v)-(b-theta • w+(t+theta) • w)
      = (a+t • v)-(b+t • w) :=
  KineticSupport.contact_time_shift a b v w t theta

theorem compose_raw (a v : E) (s t : ℝ) :
    (a-s • v)-t • v = a-(s+t) • v :=
  KineticSupport.affine_shift_compose a v s t

-- This wrapper deliberately has no inner-product or real-vector assumption.
theorem replacement_raw {F : Type*} [NormedAddCommGroup F]
    {I : Type*} [Fintype I] [DecidableEq I] (u z : I → F) (i j : I)
    (distinct : i ≠ j)
    (outside : ∀ k, k ≠ i → k ≠ j → z k = u k)
    (pair : ‖z i‖^2+‖z j‖^2=‖u i‖^2+‖u j‖^2) :
    ∑ k, ‖z k‖^2 = ∑ k, ‖u k‖^2 :=
  KineticSupport.total_energy_of_pair_replacement u z i j distinct outside pair

theorem simultaneous_raw {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → E) (i j : I) (distinct : i ≠ j) (n : E)
    (unit : inner ℝ n n=1) :
    ∑ k, ‖(Function.update
      (Function.update u i (u i - inner ℝ (u i-u j) n • n))
      j (u j + inner ℝ (u i-u j) n • n)) k‖^2 = ∑ k, ‖u k‖^2 := by
  exact KineticSupport.total_collision_energy u i j distinct n unit

theorem exponents_raw :
    (-1:ℚ)+(21/20)*(21/22)=1/440 ∧
    (-1:ℚ)+(3/2)*(4/8)= -1/4 ∧
    (1:ℚ)+4*(1/8)≤2 := KineticSupport.exponent_budget

-- Inspect the concrete map at both changed labels: both right sides use u.
theorem old_left {I : Type*} [DecidableEq I] (u : I → E)
    (i j : I) (distinct : i ≠ j) (n : E) :
    KineticSupport.pairVelocity u i j n i =
      KineticSupport.leftVelocity (u i) (u j) n := by
  simp [KineticSupport.pairVelocity, distinct]

theorem old_right {I : Type*} [DecidableEq I] (u : I → E)
    (i j : I) (n : E) :
    KineticSupport.pairVelocity u i j n j =
      KineticSupport.rightVelocity (u i) (u j) n := by
  simp [KineticSupport.pairVelocity]

-- Exact semantic counterchecks: these false extensions must not be claimed.
theorem nonunit_fails :
    ‖KineticSupport.leftVelocity (1:ℝ) 0 2‖^2 +
      ‖KineticSupport.rightVelocity (1:ℝ) 0 2‖^2 ≠ ‖(1:ℝ)‖^2+‖(0:ℝ)‖^2 := by
  norm_num [KineticSupport.leftVelocity, KineticSupport.rightVelocity,
    Real.inner_apply, smul_eq_mul]

theorem sequential_fails :
    let left := KineticSupport.leftVelocity (1:ℝ) 0 1
    let wrongRight := KineticSupport.rightVelocity left 0 1
    ‖left‖^2+‖wrongRight‖^2 ≠ ‖(1:ℝ)‖^2+‖(0:ℝ)‖^2 := by
  norm_num [KineticSupport.leftVelocity, KineticSupport.rightVelocity,
    Real.inner_apply, smul_eq_mul]

theorem wrong_shift_sign_fails :
    ((0:ℝ)+(1:ℝ)*(1:ℝ))+(0+1)*1 ≠ 0+0*1 := by norm_num

#print axioms momentum_raw
#print axioms energy_raw
#print axioms affine_raw
#print axioms relative_raw
#print axioms contact_raw
#print axioms compose_raw
#print axioms replacement_raw
#print axioms simultaneous_raw
#print axioms exponents_raw
#print axioms old_left
#print axioms old_right
#print axioms nonunit_fails
#print axioms sequential_fails
#print axioms wrong_shift_sign_fails
end IndependentAudit

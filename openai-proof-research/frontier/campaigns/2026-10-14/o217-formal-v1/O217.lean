/- Copyright 2026 Myeongjin Kang. Released under the MIT license.

Scoped formal support for O217 (zero-field SK fluctuation universality with only a
fourth-moment bound). This file is support, not the full theorem: probability,
cumulant derivative bounds, Lindeberg replacement, integrability, the stipulated
Gaussian source theorem and the weak-limit transfer remain human mathematics
unless separately formalized.

Interface disclosure:
* An `Edge n` is the ordered pair (i, j) with i < j, the canonical representative
  of the unordered pair {i, j}; this matches the 1 <= i < j <= n convention of
  the frozen scope exactly, so m = |Edge n| = n * (n - 1) / 2.
* A spin configuration is a function `Fin n -> Bool`; the sign map sends
  `false` to (1 : ℝ) and `true` to (-1 : ℝ).
* `flipSpin i` is the concrete Ising vertex flip (an involutive permutation of
  spin configurations); `flipDisorder i` negates exactly the disorder
  coordinates on edges incident to i.
* `thirdDerivLog q x e` is the third derivative in the replaced e-coordinate,
  evaluated at replacement value 0, of the log of the actual finite exponential
  partition sum.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace O217

/-! ### Finite edge set and cardinality -/

/-- Unordered pair {i, j} with i < j, as the subtype of ordered pairs with i < j. -/
abbrev Edge (n : ℕ) := Subtype (fun p : Fin n × Fin n => p.1 < p.2)

instance spinNonempty {n : ℕ} : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩

theorem edge_card (n : ℕ) : Fintype.card (Edge n) = n * (n - 1) / 2 := by
  classical
  rw [Fintype.card_subtype]
  simpa [Nat.choose_two_right] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

theorem edge_card_bound (n : ℕ) : 2 * Fintype.card (Edge n) ≤ n * n := by
  rw [edge_card, Nat.mul_comm 2]
  exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))

/-! ### Concrete Ising gauge -/

/-- Edge incident to the given vertex. -/
abbrev incident {n : ℕ} (i : Fin n) (e : Edge n) : Prop := e.val.1 = i ∨ e.val.2 = i

/-- Sign of a Boolean spin: `false` ↦ 1, `true` ↦ -1. -/
def spinSign (b : Bool) : ℝ := if b then -1 else 1

theorem spinSign_not (b : Bool) : spinSign (!b) = -spinSign b := by
  cases b <;> simp [spinSign]

/-- Product of the endpoint spins along an edge. -/
def edgeSpin {n : ℕ} (σ : Fin n → Bool) (e : Edge n) : ℝ :=
  spinSign (σ e.val.1) * spinSign (σ e.val.2)

/-- Flip the spin at vertex i only. -/
def flipSpin {n : ℕ} (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = i then !σ j else σ j

theorem flipSpin_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipSpin i) := by
  intro σ
  funext j
  by_cases h : j = i <;> simp [flipSpin, h]

/-- The vertex flip as an explicit permutation of spin configurations. -/
def flipSpinEquiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := flipSpin i σ
  invFun σ := flipSpin i σ
  left_inv σ := flipSpin_involutive i σ
  right_inv σ := flipSpin_involutive i σ

theorem sum_flipSpin {n : ℕ} (i : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin n → Bool, F (flipSpin i σ) = ∑ σ : Fin n → Bool, F σ :=
  Equiv.sum_comp (flipSpinEquiv i) F

theorem edgeSpin_flip {n : ℕ} (i : Fin n) (σ : Fin n → Bool) (e : Edge n) :
    edgeSpin (flipSpin i σ) e = (if incident i e then (-1 : ℝ) else 1) * edgeSpin σ e := by
  by_cases h1 : e.val.1 = i
  · by_cases h2 : e.val.2 = i
    · exact False.elim ((ne_of_lt e.2) (h1.trans h2.symm))
    · have h1' : spinSign ((flipSpin i σ) e.val.1) = -spinSign (σ e.val.1) := by
        show spinSign (if e.val.1 = i then !σ e.val.1 else σ e.val.1)
          = -spinSign (σ e.val.1)
        rw [ite_eq_left h1, spinSign_not]
      have h2' : spinSign ((flipSpin i σ) e.val.2) = spinSign (σ e.val.2) := by
        show spinSign (if e.val.2 = i then !σ e.val.2 else σ e.val.2)
          = spinSign (σ e.val.2)
        rw [ite_eq_right h2]
      have hf : edgeSpin (flipSpin i σ) e = -edgeSpin σ e := by
        calc edgeSpin (flipSpin i σ) e
            = spinSign ((flipSpin i σ) e.val.1) * spinSign ((flipSpin i σ) e.val.2) := rfl
          _ = -spinSign (σ e.val.1) * spinSign (σ e.val.2) := by rw [h1', h2']
          _ = -(spinSign (σ e.val.1) * spinSign (σ e.val.2)) := by ring
          _ = -edgeSpin σ e := rfl
      rw [hf, ite_eq_left (Or.inl h1)]
      ring
  · by_cases h2 : e.val.2 = i
    · have h1' : spinSign ((flipSpin i σ) e.val.1) = spinSign (σ e.val.1) := by
        show spinSign (if e.val.1 = i then !σ e.val.1 else σ e.val.1)
          = spinSign (σ e.val.1)
        rw [ite_eq_right h1]
      have h2' : spinSign ((flipSpin i σ) e.val.2) = -spinSign (σ e.val.2) := by
        show spinSign (if e.val.2 = i then !σ e.val.2 else σ e.val.2)
          = -spinSign (σ e.val.2)
        rw [ite_eq_left h2, spinSign_not]
      have hf : edgeSpin (flipSpin i σ) e = -edgeSpin σ e := by
        calc edgeSpin (flipSpin i σ) e
            = spinSign ((flipSpin i σ) e.val.1) * spinSign ((flipSpin i σ) e.val.2) := rfl
          _ = spinSign (σ e.val.1) * -spinSign (σ e.val.2) := by rw [h1', h2']
          _ = -(spinSign (σ e.val.1) * spinSign (σ e.val.2)) := by ring
          _ = -edgeSpin σ e := rfl
      rw [hf, ite_eq_left (Or.inr h2)]
      ring
    · have hf : edgeSpin (flipSpin i σ) e = edgeSpin σ e := by
        calc edgeSpin (flipSpin i σ) e
            = spinSign ((flipSpin i σ) e.val.1) * spinSign ((flipSpin i σ) e.val.2) := rfl
          _ = spinSign (σ e.val.1) * spinSign (σ e.val.2) := by
              show spinSign (if e.val.1 = i then !σ e.val.1 else σ e.val.1)
                  * spinSign (if e.val.2 = i then !σ e.val.2 else σ e.val.2)
                = spinSign (σ e.val.1) * spinSign (σ e.val.2)
              rw [ite_eq_right h1, ite_eq_right h2]
          _ = edgeSpin σ e := rfl
      rw [hf, ite_eq_right (not_or.mpr ⟨h1, h2⟩), one_mul]

/-- Negate exactly the disorder coordinates on edges incident to i. -/
def flipDisorder {n : ℕ} (i : Fin n) (x : Edge n → ℝ) : Edge n → ℝ :=
  fun e => if incident i e then -x e else x e

theorem flipDisorder_apply {n : ℕ} (i : Fin n) (x : Edge n → ℝ) (e : Edge n) :
    (flipDisorder i x) e = if incident i e then -x e else x e := rfl

/-- Negate exactly the star coordinates: edges incident to i other than e. -/
def flipStar {n : ℕ} (i : Fin n) (e : Edge n) (x : Edge n → ℝ) : Edge n → ℝ :=
  fun f => if f ≠ e ∧ incident i f then -x f else x f

theorem flipStar_apply {n : ℕ} (i : Fin n) (e : Edge n) (x : Edge n → ℝ) (f : Edge n) :
    (flipStar i e x) f = if f ≠ e ∧ incident i f then -x f else x f := rfl

/-- Zero-field Ising Hamiltonian: sum of x_e σ_i σ_j over the edges. -/
def hamiltonian {n : ℕ} (x : Edge n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ e : Edge n, x e * edgeSpin σ e

theorem hamiltonian_flip {n : ℕ} (i : Fin n) (x : Edge n → ℝ) (σ : Fin n → Bool) :
    hamiltonian (flipDisorder i x) σ = hamiltonian x (flipSpin i σ) := by
  simp only [hamiltonian]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : incident i e
  · have hflip := edgeSpin_flip i σ e
    rw [ite_eq_left h] at hflip
    show (flipDisorder i x) e * edgeSpin σ e = x e * edgeSpin (flipSpin i σ) e
    rw [hflip, flipDisorder_apply, ite_eq_left h]
    ring
  · have hflip := edgeSpin_flip i σ e
    rw [ite_eq_right h] at hflip
    show (flipDisorder i x) e * edgeSpin σ e = x e * edgeSpin (flipSpin i σ) e
    rw [hflip, flipDisorder_apply, ite_eq_right h]
    ring

theorem hamiltonian_update_flipStar {n : ℕ} (x : Edge n → ℝ) (i : Fin n) (e : Edge n)
    (hE : incident i e) (t : ℝ) (σ : Fin n → Bool) :
    hamiltonian (Function.update (flipStar i e x) e t) σ
      = hamiltonian (Function.update x e (-t)) (flipSpin i σ) := by
  simp only [hamiltonian]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Function.update_apply, flipStar_apply]
  have hflip := edgeSpin_flip i σ f
  by_cases hf : f = e
  · rw [ite_eq_left hf, ite_eq_left hf, hflip]
    have hinc : incident i f := by rw [hf]; exact hE
    rw [ite_eq_left hinc]
    ring
  · rw [ite_eq_right hf, ite_eq_right hf, hflip]
    by_cases hinc : incident i f
    · rw [ite_eq_left ⟨hf, hinc⟩, ite_eq_left hinc]
      ring
    · rw [ite_eq_right (fun h => hinc h.2), ite_eq_right hinc]
      ring

/-- The actual finite exponential partition sum of the zero-field model. -/
def partitionSum {n : ℕ} (q : ℝ) (x : Edge n → ℝ) : ℝ :=
  ∑ σ : Fin n → Bool, Real.exp (q * hamiltonian x σ)

theorem partitionSum_pos {n : ℕ} (q : ℝ) (x : Edge n → ℝ) : 0 < partitionSum q x := by
  rw [partitionSum]
  exact Finset.sum_pos (fun σ _ => Real.exp_pos _) ⟨fun _ => false, Finset.mem_univ _⟩

theorem partitionSum_flip {n : ℕ} (q : ℝ) (i : Fin n) (x : Edge n → ℝ) :
    partitionSum q (flipDisorder i x) = partitionSum q x := by
  simp only [partitionSum]
  rw [Finset.sum_congr rfl (fun σ _ => by rw [hamiltonian_flip i x σ])]
  rw [sum_flipSpin i (fun σ => Real.exp (q * hamiltonian x σ))]

/-- Log partition function of the actual finite model. -/
def logPartition {n : ℕ} (q : ℝ) (x : Edge n → ℝ) : ℝ := Real.log (partitionSum q x)

theorem logPartition_flip {n : ℕ} (q : ℝ) (i : Fin n) (x : Edge n → ℝ) :
    logPartition q (flipDisorder i x) = logPartition q x := by
  simp only [logPartition]
  rw [partitionSum_flip]

/-! ### Deleted-edge one-parameter family and oddness of its cubic derivative -/

/-- Log of the actual finite partition sum with one coordinate replaced. -/
def logFam {n : ℕ} (q : ℝ) (x : Edge n → ℝ) (e : Edge n) : ℝ → ℝ :=
  fun t => logPartition q (Function.update x e t)

/-- The actual one-coordinate log partition is smooth of every finite order. -/
theorem logFam_contDiff {n : ℕ} (q : ℝ) (x : Edge n → ℝ) (e : Edge n) :
    ContDiff ℝ (⊤ : ℕ∞) (logFam q x e) := by
  unfold logFam logPartition
  apply ContDiff.log _ (fun t => ne_of_gt (partitionSum_pos q (Function.update x e t)))
  unfold partitionSum hamiltonian
  apply ContDiff.sum
  intro σ _
  apply ContDiff.exp
  apply contDiff_const.mul
  apply ContDiff.sum
  intro f _
  simp only [Function.update_apply]
  split_ifs <;> fun_prop

theorem logFam_flipStar {n : ℕ} (q : ℝ) (x : Edge n → ℝ) (i : Fin n) (e : Edge n)
    (hE : incident i e) (t : ℝ) :
    logFam q (flipStar i e x) e t = logFam q x e (-t) := by
  unfold logFam logPartition partitionSum
  congr 1
  calc
    _ = ∑ σ : Fin n → Bool,
        Real.exp (q * hamiltonian (Function.update x e (-t)) (flipSpin i σ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [hamiltonian_update_flipStar x i e hE t σ]
    _ = _ := sum_flipSpin i (fun σ => Real.exp (q * hamiltonian (Function.update x e (-t)) σ))

/-- The total derivative operation respects three successive sign changes.
No differentiability premise is hidden: mathlib's derivative is zero at
nondifferentiable points, and these identities also respect that convention. -/
theorem third_deriv_neg_comp (f : ℝ → ℝ) :
    deriv (deriv (deriv (fun t => f (-t)))) 0 = -deriv (deriv (deriv f)) 0 := by
  have h1 : deriv (fun t => f (-t)) = fun t => -deriv f (-t) :=
    funext (deriv_comp_neg f)
  have h2 : deriv (fun t => -deriv f (-t)) = fun t => deriv (deriv f) (-t) := by
    funext t
    rw [deriv.fun_neg, deriv_comp_neg, neg_neg]
  rw [h1, h2, deriv_comp_neg, neg_zero]

/-- Actual deleted-coordinate cubic derivative of log partition. -/
def thirdDerivLog {n : ℕ} (q : ℝ) (x : Edge n → ℝ) (e : Edge n) : ℝ :=
  deriv (deriv (deriv (logFam q x e))) 0

theorem thirdDerivLog_flipStar_odd {n : ℕ} (q : ℝ) (x : Edge n → ℝ) (i : Fin n)
    (e : Edge n) (hE : incident i e) :
    thirdDerivLog q (flipStar i e x) e = -thirdDerivLog q x e := by
  unfold thirdDerivLog
  rw [show logFam q (flipStar i e x) e = (fun t => logFam q x e (-t)) from
    funext (logFam_flipStar q x i e hE)]
  exact third_deriv_neg_comp _

/-- Cubic derivative of an observable of the actual log partition, at a deleted edge. -/
def thirdDerivObservable {n : ℕ} (Ψ : ℝ → ℝ) (q : ℝ) (x : Edge n → ℝ)
    (e : Edge n) : ℝ :=
  deriv (deriv (deriv (fun t => Ψ (logFam q x e t)))) 0

/-- Includes the square observable and scaled smooth tests. The oddness itself
requires no derivative bound or probability-law symmetry. -/
theorem thirdDerivObservable_flipStar_odd {n : ℕ} (Ψ : ℝ → ℝ) (q : ℝ)
    (x : Edge n → ℝ) (i : Fin n) (e : Edge n) (hE : incident i e) :
    thirdDerivObservable Ψ q (flipStar i e x) e = -thirdDerivObservable Ψ q x e := by
  unfold thirdDerivObservable
  rw [show (fun t => Ψ (logFam q (flipStar i e x) e t)) =
      (fun t => Ψ (logFam q x e (-t))) from
    funext (fun t => congrArg Ψ (logFam_flipStar q x i e hE t))]
  exact third_deriv_neg_comp (fun t => Ψ (logFam q x e t))

/-! ### Exact square-Taylor remainder identity (no fifth moment) -/

/-- Exact algebraic identity (18) of the candidate: the square of a one-variable
function equals its quadratic-and-cubic square Taylor data plus the two
bracketed remainder terms. No Taylor hypothesis is used; this is pure algebra. -/
theorem square_taylor_identity (u : ℝ → ℝ) (b₁ b₂ z : ℝ) :
    u z ^ 2 - b₁ ^ 2 * z ^ 2 - b₁ * b₂ * z ^ 3
      = 2 * b₁ * z * (u z - b₁ * z - b₂ * z ^ 2 / 2) + (u z - b₁ * z) ^ 2 := by
  ring

theorem square_remainder_bound (u : ℝ → ℝ) (b₁ b₂ c₁ c₂ d₁ z : ℝ)
    (hc₂ : 0 ≤ c₂) (hd : |b₁| ≤ d₁)
    (h1 : |u z - b₁ * z| ≤ c₁ * |z| ^ 2)
    (h2 : |u z - b₁ * z - b₂ * z ^ 2 / 2| ≤ c₂ * |z| ^ 3) :
    |u z ^ 2 - b₁ ^ 2 * z ^ 2 - b₁ * b₂ * z ^ 3|
      ≤ (2 * d₁ * c₂ + c₁ ^ 2) * |z| ^ 4 := by
  rw [square_taylor_identity]
  have t1 : |2 * b₁ * z * (u z - b₁ * z - b₂ * z ^ 2 / 2)|
      ≤ 2 * d₁ * c₂ * |z| ^ 4 := by
    simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    calc
      2 * |b₁| * |z| * |u z - b₁ * z - b₂ * z ^ 2 / 2|
        ≤ 2 * |b₁| * |z| * (c₂ * |z| ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = |b₁| * (2 * c₂ * |z| ^ 4) := by ring
      _ ≤ d₁ * (2 * c₂ * |z| ^ 4) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by ring
  have t2 : |(u z - b₁ * z) ^ 2| ≤ c₁ ^ 2 * |z| ^ 4 := by
    have h := mul_self_le_mul_self (abs_nonneg (u z - b₁ * z)) h1
    rw [abs_pow]
    nlinarith only [h]
  calc
    _ ≤ |2 * b₁ * z * (u z - b₁ * z - b₂ * z ^ 2 / 2)| +
        |(u z - b₁ * z) ^ 2| := abs_add_le _ _
    _ ≤ 2 * d₁ * c₂ * |z| ^ 4 + c₁ ^ 2 * |z| ^ 4 := add_le_add t1 t2
    _ = _ := by ring

/-- Generic form of the candidate's square remainder (19): the fourth-order
square remainder is bounded using only first/second/third-order Taylor
remainder bounds and |b₁| ≤ d₁. The sought fourth-order square estimate is the
conclusion, never a hypothesis. -/
theorem square_taylor_remainder_H (u : ℝ → ℝ) (H₀ b₁ b₂ b₃ c₁ c₂ c₃ d₁ z : ℝ)
    (hc₂ : 0 ≤ c₂) (hd : |b₁| ≤ d₁)
    (h1 : |u z - b₁ * z| ≤ c₁ * |z| ^ 2)
    (h2 : |u z - b₁ * z - b₂ * z ^ 2 / 2| ≤ c₂ * |z| ^ 3)
    (h3 : |u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6| ≤ c₃ * |z| ^ 4) :
    |(H₀ + u z) ^ 2 - (H₀ ^ 2
        + 2 * H₀ * (b₁ * z + b₂ * z ^ 2 / 2 + b₃ * z ^ 3 / 6)
        + b₁ ^ 2 * z ^ 2 + b₁ * b₂ * z ^ 3)|
      ≤ (2 * |H₀| * c₃ + (2 * d₁ * c₂ + c₁ ^ 2)) * |z| ^ 4 := by
  have hsplit : (H₀ + u z) ^ 2 - (H₀ ^ 2
      + 2 * H₀ * (b₁ * z + b₂ * z ^ 2 / 2 + b₃ * z ^ 3 / 6)
      + b₁ ^ 2 * z ^ 2 + b₁ * b₂ * z ^ 3)
      = 2 * H₀ * (u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6)
        + (u z ^ 2 - b₁ ^ 2 * z ^ 2 - b₁ * b₂ * z ^ 3) := by ring
  rw [hsplit]
  have hA : |2 * H₀ * (u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6)|
      ≤ 2 * |H₀| * c₃ * |z| ^ 4 := by
    have habs : |2 * H₀ * (u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6)|
        = 2 * |H₀| * |u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    calc 2 * |H₀| * |u z - b₁ * z - b₂ * z ^ 2 / 2 - b₃ * z ^ 3 / 6|
        ≤ 2 * |H₀| * (c₃ * |z| ^ 4) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * |H₀| * c₃ * |z| ^ 4 := by ring
  have hB := square_remainder_bound u b₁ b₂ c₁ c₂ d₁ z hc₂ hd h1 h2
  have hring : (2 * |H₀| * c₃ + (2 * d₁ * c₂ + c₁ ^ 2)) * |z| ^ 4
      = (2 * |H₀| * c₃) * |z| ^ 4 + (2 * d₁ * c₂ + c₁ ^ 2) * |z| ^ 4 := by ring
  rw [hring]
  exact (abs_add_le _ _).trans (add_le_add hA hB)

/-! ### Noncircular real quadratic bootstrap -/

theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hprod : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hsq : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hprod]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = |Real.sqrt a + Real.sqrt b| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt a + Real.sqrt b :=
        abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))

/-- Candidate (27), with an explicit constant: if the finite maximum M satisfies
the bootstrapped quadratic inequality M ≤ V + C √M + C, then
√M ≤ √V + C + √C. The argument is algebraic, never an iteration assuming the
conclusion. -/
theorem quadratic_bootstrap (M V C : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (h : M ≤ V + C * Real.sqrt M + C) :
    Real.sqrt M ≤ Real.sqrt V + C + Real.sqrt C := by
  have hMy : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM
  have hexp : (Real.sqrt M - C / 2) ^ 2
      = (Real.sqrt M) ^ 2 - C * Real.sqrt M + C ^ 2 / 4 := by ring
  have hsq : (Real.sqrt M - C / 2) ^ 2 ≤ V + C + C ^ 2 / 4 := by
    rw [hexp, hMy]
    linarith [h]
  have habs : Real.sqrt M - C / 2 ≤ Real.sqrt ((Real.sqrt M - C / 2) ^ 2) := by
    calc Real.sqrt M - C / 2 ≤ |Real.sqrt M - C / 2| := le_abs_self _
      _ = Real.sqrt ((Real.sqrt M - C / 2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  have hmono : Real.sqrt ((Real.sqrt M - C / 2) ^ 2) ≤ Real.sqrt (V + C + C ^ 2 / 4) :=
    Real.sqrt_le_sqrt hsq
  have h1 := sqrt_add_le V (C + C ^ 2 / 4) hV (add_nonneg hC (by positivity))
  have h2 := sqrt_add_le C (C ^ 2 / 4) hC (by positivity)
  have hsqrt4 : Real.sqrt (C ^ 2 / 4) = C / 2 := by
    have hq : C ^ 2 / 4 = (C / 2) ^ 2 := by ring
    rw [hq, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ C / 2)]
  have hfinal : Real.sqrt M
      ≤ C / 2 + Real.sqrt V + (Real.sqrt C + C / 2) := by
    rw [← add_assoc] at h1
    linarith [habs, hmono, h1, h2, hsqrt4]
  linarith

/-- Substitution step (26)→(28): every member bound C(√M+1) becomes
C(√V + C + √C + 1) via the bootstrap. -/
theorem bootstrap_variance (A M V C : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hA : |A - V| ≤ C * (Real.sqrt M + 1)) (hboot : M ≤ V + C * Real.sqrt M + C) :
    |A - V| ≤ C * (Real.sqrt V + C + Real.sqrt C + 1) := by
  have hboot' := quadratic_bootstrap M V C hM hV hC hboot
  have h1 : C * (Real.sqrt M + 1) ≤ C * (Real.sqrt V + C + Real.sqrt C + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hboot']) hC
  linarith [hA, h1]

/-- Exact centered-variance correction: subtracting the squared mean offset
costs at most the square of the mean bound. -/
theorem centered_variance (A m V C₂ C₃ : ℝ)
    (hA : |A - V| ≤ C₂ * (1 + Real.sqrt V)) (hm : |m| ≤ C₃) :
    |A - m ^ 2 - V| ≤ C₂ * (1 + Real.sqrt V) + C₃ ^ 2 := by
  have hm2 : m ^ 2 ≤ C₃ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg m) hm
    nlinarith [sq_abs m]
  calc |A - m ^ 2 - V| = |(A - V) - m ^ 2| := by congr 1; ring
    _ ≤ |A - V| + |m ^ 2| := abs_sub _ _
    _ = |A - V| + m ^ 2 := by rw [abs_of_nonneg (sq_nonneg m)]
    _ ≤ C₂ * (1 + Real.sqrt V) + C₃ ^ 2 := add_le_add hA hm2

/-- Scalar assembly of the bootstrap and the exact mean-square correction.
`A` stands for a square moment, and `mean` for the mean offset; the probability
identities establishing that interpretation are outside this file. -/
theorem centered_variance_from_bootstrap (A mean M V C B : ℝ)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hboot : M ≤ V + C * Real.sqrt M + C)
    (hA : |A - V| ≤ C * (Real.sqrt M + 1)) (hm : |mean| ≤ B) :
    |A - mean ^ 2 - V| ≤
      (C * (C + Real.sqrt C + 1) + B ^ 2) * (1 + Real.sqrt V) := by
  have ha := bootstrap_variance A M V C hV hM hC hA hboot
  have hm2 : mean ^ 2 ≤ B ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg mean) hm
    nlinarith [sq_abs mean]
  have hab : |A - mean ^ 2 - V| ≤ |A - V| + mean ^ 2 := by
    calc
      _ = |(A - V) - mean ^ 2| := by congr 1; ring
      _ ≤ |A - V| + |mean ^ 2| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (sq_nonneg mean)]
  have hx : 0 ≤ C * (C + Real.sqrt C) * Real.sqrt V := by positivity
  have hy : 0 ≤ B ^ 2 * Real.sqrt V := by positivity
  nlinarith [Real.sqrt_nonneg C, Real.sqrt_nonneg V]

/-! ### Finite n cancellation of the edge-count powers -/

/-- Human (14), using the actual edge cardinality. -/
theorem mq4_le (β : ℝ) (n : ℕ) (hn : 0 < (n : ℝ)) :
    (Fintype.card (Edge n) : ℝ) * (β / Real.sqrt (n : ℝ)) ^ 4 ≤ β ^ 4 / 2 := by
  have hc : 2 * (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    norm_cast
    simpa [pow_two] using (edge_card_bound n)
  have hpow : (β / Real.sqrt (n : ℝ)) ^ 4 = β ^ 4 / (n : ℝ) ^ 2 := by
    rw [div_pow]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hn.le]
  rw [hpow]
  have h := mul_le_mul_of_nonneg_right hc (show 0 ≤ β ^ 4 by positivity)
  apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
  field_simp
  nlinarith only [h]

theorem mnq6_le (β : ℝ) (n : ℕ) (hn : 0 < (n : ℝ)) :
    (Fintype.card (Edge n) : ℝ) * (n : ℝ) * (β / Real.sqrt (n : ℝ)) ^ 6 ≤ β ^ 6 / 2 := by
  have hc : 2 * (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    norm_cast
    simpa [pow_two] using (edge_card_bound n)
  have hpow : (β / Real.sqrt (n : ℝ)) ^ 6 = β ^ 6 / (n : ℝ) ^ 3 := by
    rw [div_pow]
    congr 1
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hn.le]
  rw [hpow]
  have h := mul_le_mul_of_nonneg_right hc (show 0 ≤ β ^ 6 by positivity)
  apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
  field_simp
  nlinarith only [h]

end O217

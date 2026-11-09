/-
  UNCOMPILED DRAFT (expanded-corpus-r125 lane; Lean/lake were NOT run in this lane by instruction).
  Target: MathDB 344002 = Graham, arXiv:1910.00924v1, Conjecture 3.3 (label conjexceptionalZprime):
    "If p is prime and 1 < n < p, all the extreme n-element subsets of Z_p are equivalent."
  We prove the literal negation with p = 71, n = 25.

  Source definitions (Graham, Def. 1.1 and Subsec. "Automorphisms and equivalent sets"):
  * The Fourier transform of a measure mu on the discrete group Z_p is evaluated at all characters
    chi_k(x) = exp(2 pi i k x / p), k in Z_p (the dual group).
  * A nonzero measure mu is extreme if ||mu-hat||_infty = ||mu|| / sqrt(# supp mu).
  * A finite set E is extreme if it is the support of an extreme measure.
  * E, F are equivalent if one is obtained from the other by a sequence of group automorphisms and
    translations.  We encode this literally as the reflexive-transitive closure of the one-step relation
    "F = image of E under an additive automorphism, or under a translation".  (Sequences in either
    direction are covered because the inverse of each step is again a step; we only need that the
    invariant `apCount` is preserved by each step, which makes non-equivalence follow for the closure.)

  Proof idea: two explicit {-1,0,1}-valued sequences c1, c2 on Z_71 with perfect periodic
  autocorrelation (sum_x c(x) c(x+g) = 25 [g = 0]), i.e. circulant weighing matrices CW(71,25).
  Then |mu-hat| = 5 identically, ||mu|| = 25 and # supp = 25, so both supports are extreme.
  The affine-invariant apCount E = #{(x,y) in E x E : 2y - x in E} is 225 for E1 and 205 for E2.

  Statement-fidelity points for review: (1) dual group = all k : ZMod 71; (2) "extreme set" requires
  supp mu = E exactly; (3) equivalence = closure under automorphisms and translations.
-/
import Mathlib

open Finset Complex

namespace Graham344002

variable {p : ℕ} [NeZero p]

/-- The character `x ↦ exp(-2πi k x / p)` of `ZMod p`, via Mathlib's `ZMod.toCircle`. -/
noncomputable def chi (k x : ZMod p) : ℂ := (ZMod.toCircle (-(k * x)) : ℂ)

/-- Fourier–Stieltjes transform of a (finitely supported) measure `μ` on `ZMod p`. -/
noncomputable def fourier (μ : ZMod p → ℂ) (k : ZMod p) : ℂ := ∑ x, μ x * chi k x

/-- Support of a measure. -/
def supp (μ : ZMod p → ℂ) : Finset (ZMod p) := univ.filter (fun x => μ x ≠ 0)

/-- Graham's Definition 1.1 (extreme measure). `‖μ‖` is the total variation `∑ |μ{x}|`. -/
def IsExtremeMeasure (μ : ZMod p → ℂ) : Prop :=
  μ ≠ 0 ∧ (⨆ k : ZMod p, ‖fourier μ k‖) = (∑ x, ‖μ x‖) / Real.sqrt ((supp μ).card : ℝ)

/-- Graham's Definition 1.1 (extreme set). -/
def IsExtremeSet (E : Finset (ZMod p)) : Prop :=
  ∃ μ : ZMod p → ℂ, IsExtremeMeasure μ ∧ supp μ = E

/-- One step: image under an additive automorphism, or under a translation. -/
def Step (E F : Finset (ZMod p)) : Prop :=
  (∃ φ : ZMod p ≃+ ZMod p, F = E.image φ) ∨ (∃ b : ZMod p, F = E.image (· + b))

/-- Graham's equivalence: obtainable by a (finite) sequence of automorphisms and translations. -/
def Equivalent (E F : Finset (ZMod p)) : Prop := Relation.ReflTransGen Step E F

/-- The literal MathDB 344002 statement. -/
def Conjecture : Prop :=
  ∀ (q : ℕ) (hq : q.Prime), haveI : NeZero q := ⟨hq.ne_zero⟩;
    ∀ n : ℕ, 1 < n → n < q → ∀ E F : Finset (ZMod q), E.card = n → F.card = n →
      IsExtremeSet E → IsExtremeSet F → Equivalent E F

/-! ### Invariant -/

/-- Number of pairs `(x, y) ∈ E × E` with `2y - x ∈ E` (three-term progressions, ordered). -/
def apCount (E : Finset (ZMod p)) : ℕ := ((E ×ˢ E).filter (fun xy => 2 * xy.2 - xy.1 ∈ E)).card

lemma apCount_image_injective (E : Finset (ZMod p)) (f : ZMod p → ZMod p) (hf : Function.Injective f)
    (hlin : ∀ x y, f (2 * y - x) = 2 * f y - f x) : apCount (E.image f) = apCount E := by
  -- bijection (x,y) ↦ (f x, f y) between the two filtered product sets
  unfold apCount
  symm
  refine Finset.card_bij (fun xy _ => (f xy.1, f xy.2)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
    refine ⟨⟨Finset.mem_image_of_mem f h.1.1, Finset.mem_image_of_mem f h.1.2⟩, ?_⟩
    rw [← hlin]; exact Finset.mem_image_of_mem f h.2
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨hf h.1, hf h.2⟩
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at h
    obtain ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, hz⟩ := h
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hy⟩, ?_⟩
    rw [← hlin] at hz
    obtain ⟨z, hz', hfz⟩ := hz
    rwa [← hf hfz]

lemma apCount_step {E F : Finset (ZMod p)} (h : Step E F) : apCount F = apCount E := by
  rcases h with ⟨φ, rfl⟩ | ⟨b, rfl⟩
  · exact apCount_image_injective E φ φ.injective (fun x y => by
      simp [map_sub, two_mul, map_add])
  · exact apCount_image_injective E (· + b) (add_left_injective b) (fun x y => by ring)

lemma apCount_equivalent {E F : Finset (ZMod p)} (h : Equivalent E F) : apCount F = apCount E := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [apCount_step hs, ih]

/-! ### Perfect autocorrelation gives a flat Fourier transform -/

lemma chi_mul (k x y : ZMod p) : chi k x * chi k y = chi k (x + y) := by
  unfold chi
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring

lemma conj_chi (k x : ZMod p) : (starRingEnd ℂ) (chi k x) = chi k (-x) := by
  unfold chi
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]; congr 2; ring

lemma chi_zero (k : ZMod p) : chi k 0 = 1 := by simp [chi]

/-- If a real sequence has autocorrelation `w·[g = 0]` then `|μ̂|² = w` everywhere. -/
lemma normSq_fourier_of_perfect (c : ZMod p → ℤ) (w : ℤ)
    (hc : ∀ g : ZMod p, (∑ x, c x * c (x + g)) = if g = 0 then w else 0) (k : ZMod p) :
    Complex.normSq (fourier (fun x => (c x : ℂ)) k) = w := by
  -- ‖∑ c x χ(x)‖² = ∑_x ∑_y c x c y χ(x) conj χ(y) = ∑_g χ(-g)·(∑_x c x c (x+g)) = w
  have key : (fourier (fun x => (c x : ℂ)) k) * (starRingEnd ℂ) (fourier (fun x => (c x : ℂ)) k)
      = ∑ g : ZMod p, chi k (-g) * ((∑ x, c x * c (x + g) : ℤ) : ℂ) := by
    unfold fourier
    rw [map_sum, Finset.sum_mul_sum]
    -- reindex the inner variable y = x + g
    rw [Finset.sum_comm]
    simp only [map_mul, Complex.conj_intCast, conj_chi]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) (Finset.sum_comm)
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_addLeft, Int.cast_mul, Int.cast_sum]
    have : chi k x * chi k (-(x + g)) = chi k (-g) := by rw [chi_mul]; congr 1; ring
    calc (c x : ℂ) * chi k x * ((c (x + g) : ℂ) * chi k (-(x + g)))
        = (chi k x * chi k (-(x + g))) * ((c x : ℂ) * c (x + g)) := by ring
      _ = chi k (-g) * ((c x : ℂ) * c (x + g)) := by rw [this]
  rw [Complex.mul_conj] at key
  have h2 : (∑ g : ZMod p, chi k (-g) * ((∑ x, c x * c (x + g) : ℤ) : ℂ)) = (w : ℂ) := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · simp [hc, chi_zero]
    · intro g _ hg; simp [hc, hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact_mod_cast key.trans h2

/-! ### The certificate on ZMod 71 -/

/-- Coefficient lists (index = residue 0..70). -/
def L1 : List ℤ := [0, 1, -1, 1, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, -1, 0, 0, 1, 1, 0, 0,
  -1, 1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0,
  -1, 0, 0, 0, 0, 0, 0, 0, -1, 0]
def L2 : List ℤ := [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, 0, -1, 1, 1, 0, 0, -1, 0, 0, 1, -1, -1, -1, 1, 0, -1, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, -1, -1, 0, 0]

def c1 (x : ZMod 71) : ℤ := L1.getD x.val 0
def c2 (x : ZMod 71) : ℤ := L2.getD x.val 0

def E1 : Finset (ZMod 71) := {1, 2, 3, 4, 5, 10, 15, 18, 19, 20, 21, 24, 25, 28, 29, 32, 34, 37, 43, 49,
  50, 54, 57, 61, 69}
def E2 : Finset (ZMod 71) := {1, 2, 5, 7, 10, 22, 23, 25, 33, 35, 37, 39, 42, 43, 44, 47, 50, 51, 52, 53,
  54, 56, 57, 67, 68}

-- Finite computations (kernel `decide`; root may need `decide +kernel` or a verified Bool checker):
lemma auto1 : ∀ g : ZMod 71, (∑ x, c1 x * c1 (x + g)) = if g = 0 then 25 else 0 := by decide
lemma auto2 : ∀ g : ZMod 71, (∑ x, c2 x * c2 (x + g)) = if g = 0 then 25 else 0 := by decide
lemma supp1 : univ.filter (fun x : ZMod 71 => c1 x ≠ 0) = E1 := by decide
lemma supp2 : univ.filter (fun x : ZMod 71 => c2 x ≠ 0) = E2 := by decide
lemma abs1 : (∑ x : ZMod 71, |c1 x|) = 25 := by decide
lemma abs2 : (∑ x : ZMod 71, |c2 x|) = 25 := by decide
lemma card1 : E1.card = 25 := by decide
lemma card2 : E2.card = 25 := by decide
lemma ap1 : apCount E1 = 225 := by decide
lemma ap2 : apCount E2 = 205 := by decide

lemma extreme_of_perfect (c : ZMod 71 → ℤ) (E : Finset (ZMod 71))
    (hauto : ∀ g : ZMod 71, (∑ x, c x * c (x + g)) = if g = 0 then 25 else 0)
    (hsupp : univ.filter (fun x : ZMod 71 => c x ≠ 0) = E) (habs : (∑ x : ZMod 71, |c x|) = 25)
    (hcard : E.card = 25) : IsExtremeSet E := by
  refine ⟨fun x => (c x : ℂ), ⟨?_, ?_⟩, ?_⟩
  · intro h
    have : (∑ x : ZMod 71, |c x|) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have := congrFun h x; simp at this; simp [this]
    omega
  · have hsupp' : supp (fun x => (c x : ℂ)) = E := by
      rw [← hsupp]; unfold supp; congr 1; ext x; simp
    have hflat : ∀ k, ‖fourier (fun x => (c x : ℂ)) k‖ = 5 := by
      intro k
      have h := normSq_fourier_of_perfect c 25 hauto k
      rw [Complex.normSq_eq_norm_sq] at h
      have h0 : (0 : ℝ) ≤ ‖fourier (fun x => (c x : ℂ)) k‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖fourier (fun x => (c x : ℂ)) k‖ - 5),
                 sq_nonneg (‖fourier (fun x => (c x : ℂ)) k‖ + 5)]
    have hnorm : (∑ x : ZMod 71, ‖((c x : ℤ) : ℂ)‖) = 25 := by
      simp only [Complex.norm_intCast]
      exact_mod_cast habs
    rw [show (fun k => ‖fourier (fun x => (c x : ℂ)) k‖) = fun _ => (5 : ℝ) from funext hflat,
      ciSup_const, hsupp', hcard, hnorm]
    rw [show ((25 : ℕ) : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [← hsupp]; unfold supp; congr 1; ext x; simp

theorem not_conjecture : ¬ Conjecture := by
  intro h
  have hp : Nat.Prime 71 := by norm_num
  have := h 71 hp 25 (by norm_num) (by norm_num) E1 E2 card1 card2
    (extreme_of_perfect c1 E1 auto1 supp1 abs1 card1)
    (extreme_of_perfect c2 E2 auto2 supp2 abs2 card2)
  have := apCount_equivalent this
  rw [ap1, ap2] at this
  norm_num at this

end Graham344002

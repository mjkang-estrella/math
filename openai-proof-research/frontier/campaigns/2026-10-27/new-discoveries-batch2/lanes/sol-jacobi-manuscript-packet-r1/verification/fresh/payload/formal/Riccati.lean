import Filtration

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace JacobiShifted.BinaryFiltration

variable {R : Type*} [CommRing R]

/-- The actual coefficient convolution in `MvPolynomial`, expressed by its finite support. -/
theorem coefficient_product_expansion (f g : P R) (γ : Exponent) :
    (f * g).coeff γ = ∑ α ∈ f.support, ∑ β ∈ g.support,
      if α + β = γ then f.coeff α * g.coeff β else 0 := by
  classical
  conv_lhs => rw [f.as_sum, g.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul_monomial,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_monomial]
  exact Finset.sum_comm

theorem coefficient_square_expansion (f : P R) (γ : Exponent) :
    (f ^ 2).coeff γ = ∑ α ∈ f.support, ∑ β ∈ f.support,
      if α + β = γ then f.coeff α * f.coeff β else 0 := by
  simpa only [pow_two] using coefficient_product_expansion f f γ

/-- Finite involution pairing: a fixed index gives a square; two distinct indices
are removed together and give exactly `2 * f i * f (τ i)`. -/
theorem weighted_involution_products {ι : Type*} (s : Finset ι) (τ : ι → ι)
    (hτ : ∀ i ∈ s, τ (τ i) = i) (hs : ∀ i ∈ s, τ i ∈ s)
    (f : ι → P R) (hf : ∀ i ∈ s, Weighted (f i)) :
    Weighted (∑ i ∈ s, f i * f (τ i)) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
    · simpa using (weighted_zero (R := R))
    have hta := hs a ha
    have htta := hτ a ha
    by_cases he : τ a = a
    · have hsub : s.erase a ⊂ s := Finset.erase_ssubset ha
      have hclosed : ∀ i ∈ s.erase a, τ i ∈ s.erase a := by
        intro i hi
        refine Finset.mem_erase.mpr ⟨?_, hs i (Finset.mem_of_mem_erase hi)⟩
        intro ht
        have hit := hτ i (Finset.mem_of_mem_erase hi)
        rw [ht, he] at hit
        exact (Finset.ne_of_mem_erase hi) hit.symm
      have hw := ih (s.erase a) hsub
        (fun i hi => hτ i (Finset.mem_of_mem_erase hi)) hclosed
        (fun i hi => hf i (Finset.mem_of_mem_erase hi))
      rw [← Finset.add_sum_erase s (fun i => f i * f (τ i)) ha, he, ← pow_two]
      exact weighted_add (weighted_square (hf a ha)) hw
    · let t := (s.erase a).erase (τ a)
      have ht_sub : t ⊆ s := fun i hi => Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hi)
      have ht_strict : t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨ht_sub, ?_⟩
        intro ht
        have hat : a ∈ t := ht.symm ▸ ha
        exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hat)) rfl
      have hclosed : ∀ i ∈ t, τ i ∈ t := by
        intro i hi
        have hi_s := ht_sub hi
        have hia := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hit := Finset.ne_of_mem_erase hi
        apply Finset.mem_erase.mpr
        constructor
        · intro h
          apply hia
          have hti := hτ i hi_s
          rw [h, htta] at hti
          exact hti.symm
        · apply Finset.mem_erase.mpr
          constructor
          · intro h
            apply hit
            have hti := hτ i hi_s
            rw [h] at hti
            exact hti.symm
          · exact hs i hi_s
      have hw := ih t ht_strict (fun i hi => hτ i (ht_sub hi)) hclosed
        (fun i hi => hf i (ht_sub hi))
      have hta_erase : τ a ∈ s.erase a := Finset.mem_erase.mpr ⟨he, hta⟩
      have hsum : (∑ i ∈ s, f i * f (τ i)) =
          2 * f a * f (τ a) + ∑ i ∈ t, f i * f (τ i) := by
        rw [← Finset.add_sum_erase s (fun i => f i * f (τ i)) ha,
          ← Finset.add_sum_erase (s.erase a) (fun i => f i * f (τ i)) hta_erase,
          htta]
        dsimp [t]
        ring
      rw [hsum]
      exact weighted_add (weighted_two_mul (hf a ha) (hf (τ a) hta)) hw

/-- The only possible fixed spectral index is the middle index of an even order. -/
theorem spectral_fixed_iff (n i : ℕ) (hi : i ≤ n) :
    n - i = i ↔ n = 2 * i := by omega

theorem spectral_fixed_even_iff (n i : ℕ) (hi : i ≤ n) :
    n - i = i ↔ Even n ∧ i = n / 2 := by
  rw [spectral_fixed_iff n i hi]
  constructor
  · intro he
    constructor
    · exact ⟨i, by omega⟩
    · omega
  · rintro ⟨⟨k, hk⟩, hi⟩
    omega

/-- Each unequal spectral orbit contributes exactly this factor-two product. -/
theorem spectral_pair_identity (f g : P R) : f * g + g * f = 2 * f * g := by ring

/-- The stipulated zero initial index annihilates both convolution endpoints. -/
theorem spectral_endpoints_zero (h : ℕ → P R) (hzero : h 0 = 0) (n : ℕ) :
    h 0 * h n = 0 ∧ h n * h 0 = 0 := by simp [hzero]

/-- The full spectral convolution, including the zero-index endpoints. -/
theorem weighted_convolution (h : ℕ → P R) (n : ℕ)
    (hh : ∀ i ≤ n, Weighted (h i)) :
    Weighted (∑ i ∈ Finset.range (n + 1), h i * h (n - i)) := by
  apply weighted_involution_products (Finset.range (n + 1)) (fun i => n - i)
  · intro i hi
    have := Finset.mem_range.mp hi
    omega
  · intro i _
    apply Finset.mem_range.mpr
    omega
  · intro i hi
    exact hh i (by have := Finset.mem_range.mp hi; omega)

/-- Initial potential, with exactly the two degree-one parameter monomials. -/
def initial (A B : R) : P R :=
  MvPolynomial.monomial (Finsupp.single 0 1) A +
    MvPolynomial.monomial (Finsupp.single 1 1) B

theorem initial_eq_variables (A B : R) : initial A B =
    MvPolynomial.X 0 * MvPolynomial.C A + MvPolynomial.X 1 * MvPolynomial.C B := by
  simp only [initial, MvPolynomial.X, MvPolynomial.C_apply,
    MvPolynomial.monomial_mul_monomial, add_zero, one_mul]

theorem weighted_initial (A B : R) : Weighted (initial A B) := by
  apply weighted_add
  · apply weighted_monomial
    · simp
    · simp [weight]
  · apply weighted_monomial
    · simp
    · simp [weight]

/-- Strong induction for the genuine quadratic Riccati recurrence. The only
operator supplied is the additive coefficient map; preservation is proved internally. -/
theorem riccati_weighted (δ : R →+ R) (P₀ : P R) (h : ℕ → P R)
    (hzero : h 0 = 0) (hone : h 1 = P₀) (hP : Weighted P₀)
    (hrec : ∀ n : ℕ, 1 ≤ n → h (n + 1) = -coefficientOperator δ (h n) -
      ∑ i ∈ Finset.range (n + 1), h i * h (n - i)) :
    ∀ n : ℕ, Weighted (h n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | n
    · rw [hzero]
      exact weighted_zero
    · by_cases hn : n = 0
      · simpa [hn, hone] using hP
      · rw [hrec n (by omega), sub_eq_add_neg]
        apply weighted_add
        · exact weighted_neg (weighted_coefficientOperator δ (ih n (by omega)))
        · apply weighted_neg
          exact weighted_convolution h n (fun i hi => ih i (by omega))

/-- Convenient initial-potential specialization, valid over every commutative ring. -/
theorem riccati_initial_weighted (δ : R →+ R) (A B : R) (h : ℕ → P R)
    (hzero : h 0 = 0) (hone : h 1 = initial A B)
    (hrec : ∀ n : ℕ, 1 ≤ n → h (n + 1) = -coefficientOperator δ (h n) -
      ∑ i ∈ Finset.range (n + 1), h i * h (n - i)) :
    ∀ n : ℕ, Weighted (h n) :=
  riccati_weighted δ (initial A B) h hzero hone (weighted_initial A B) hrec

def bidegree (i j : ℕ) : Exponent := Finsupp.single 0 i + Finsupp.single 1 j

@[simp] theorem bidegree_zero_coordinate (i j : ℕ) : bidegree i j 0 = i := by
  simp [bidegree]

@[simp] theorem bidegree_one_coordinate (i j : ℕ) : bidegree i j 1 = j := by
  simp [bidegree]

theorem odd_bidegree_weight (i j : ℕ) (hj : Odd j) :
    sigma (i + j - 1) ≤ weight (bidegree i j) := by
  have hpos : 0 < j := by obtain ⟨k, hk⟩ := hj; omega
  have ho := sigma_odd_pred hj
  have hs := sigma_add_le i (j - 1)
  have he : i + j - 1 = i + (j - 1) := by omega
  rw [he]
  simp only [weight, bidegree_zero_coordinate, bidegree_one_coordinate]
  omega

theorem weighted_odd_coefficient {f : P R} (hf : Weighted f)
    (i j : ℕ) (hj : Odd j) :
    (2 : R) ^ sigma (i + j - 1) ∣ f.coeff (bidegree i j) := by
  apply dvd_trans (pow_dvd_pow (2 : R) (odd_bidegree_weight i j hj))
  apply hf.2
  intro he
  have he1 := congrArg (fun α : Exponent => α 1) he
  simp only [bidegree_one_coordinate, Finsupp.zero_apply] at he1
  obtain ⟨k, hk⟩ := hj
  omega

/-- The requested odd-second-bidegree arithmetic conclusion, with no residual
digit inequality or polynomial-closure premise. -/
theorem riccati_odd_coefficient (δ : R →+ R) (A B : R) (h : ℕ → P R)
    (hzero : h 0 = 0) (hone : h 1 = initial A B)
    (hrec : ∀ n : ℕ, 1 ≤ n → h (n + 1) = -coefficientOperator δ (h n) -
      ∑ i ∈ Finset.range (n + 1), h i * h (n - i))
    (n i j : ℕ) (hj : Odd j) :
    (2 : R) ^ sigma (i + j - 1) ∣ (h n).coeff (bidegree i j) :=
  weighted_odd_coefficient (riccati_initial_weighted δ A B h hzero hone hrec n) i j hj

/-- The same result with an explicitly named total degree. -/
theorem riccati_degree_odd_coefficient (δ : R →+ R) (A B : R) (h : ℕ → P R)
    (hzero : h 0 = 0) (hone : h 1 = initial A B)
    (hrec : ∀ n : ℕ, 1 ≤ n → h (n + 1) = -coefficientOperator δ (h n) -
      ∑ i ∈ Finset.range (n + 1), h i * h (n - i))
    (n i j d : ℕ) (hj : Odd j) (hd : d = i + j) :
    (2 : R) ^ sigma (d - 1) ∣ (h n).coeff (bidegree i j) := by
  subst d
  exact riccati_odd_coefficient δ A B h hzero hone hrec n i j hj

end JacobiShifted.BinaryFiltration

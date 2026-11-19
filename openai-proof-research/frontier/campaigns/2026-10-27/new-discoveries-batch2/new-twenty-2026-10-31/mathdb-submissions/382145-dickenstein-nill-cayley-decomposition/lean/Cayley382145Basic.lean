import Cayley382145Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # MathDB 382145: basic facts on integral pairings and lattice hulls -/

namespace Cayley382145

open Finset

variable {n : ℕ}

/-- Integer pairing. -/
def zDot (a v : Fin n → ℤ) : ℤ := ∑ i, a i * v i

/-- Real dot product. -/
def rdot {m : ℕ} (u x : Fin m → ℝ) : ℝ := ∑ k, u k * x k

theorem intDot_eq_rdot (a : Fin n → ℤ) (x : Fin n → ℝ) : intDot a x = rdot (castPt a) x := rfl

theorem intDot_castPt (a v : Fin n → ℤ) : intDot a (castPt v) = (zDot a v : ℝ) := by
  simp [intDot, castPt, zDot]

theorem rdot_sum {ι : Type*} [Fintype ι] (y : ι → ℝ) (α : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    rdot (∑ i, y i • α i) x = ∑ i, y i * rdot (α i) x := by
  simp only [rdot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring)

theorem rdot_zero_left (x : Fin n → ℝ) : rdot 0 x = 0 := by simp [rdot]

/-- `intDot a` as a real linear functional. -/
noncomputable def intDotL (a : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := intDot a
  map_add' x y := by
    simp only [intDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [intDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem intDotL_apply (a : Fin n → ℤ) (x : Fin n → ℝ) : intDotL a x = intDot a x := rfl

/-- Full dimensionality: no nonzero integral functional is constant on the generators. -/
theorem exists_ne_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {c : Fin n → ℤ} (hc : c ≠ 0) (d : ℝ) : ∃ v ∈ V, intDot c (castPt v) ≠ d := by
  by_contra h
  push Not at h
  have hsub : latticeHull V ⊆ {x | intDotL c x = d} := by
    apply convexHull_min _ (convex_hyperplane (intDotL c).isLinear d)
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have hvs : vectorSpan ℝ (latticeHull V) = ⊤ := by
    rw [← direction_affineSpan, hfull, AffineSubspace.direction_top]
  have hle : vectorSpan ℝ (latticeHull V) ≤ LinearMap.ker (intDotL c) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have h1 : intDotL c x = d := hsub hx
    have h2 : intDotL c y = d := hsub hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub, h1, h2, sub_self]
  rw [hvs] at hle
  apply hc
  funext i
  have hi := hle (Submodule.mem_top (x := (Pi.single i 1 : Fin n → ℝ)))
  rw [LinearMap.mem_ker, intDotL_apply] at hi
  simp [intDot, Pi.single_apply] at hi
  simpa using hi

theorem exists_zDot_ne_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {c : Fin n → ℤ} (hc : c ≠ 0) (d : ℤ) : ∃ v ∈ V, zDot c v ≠ d := by
  obtain ⟨v, hv, hne⟩ := exists_ne_of_full hfull hc (d : ℝ)
  refine ⟨v, hv, fun h => hne ?_⟩
  rw [intDot_castPt, h]

theorem nonempty_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    V.Nonempty := by
  rcases V.eq_empty_or_nonempty with h | h
  · subst h
    exfalso
    have hb : affineSpan ℝ (latticeHull (∅ : Finset (Fin n → ℤ))) = ⊥ := by
      simp [latticeHull]
    rw [hb] at hfull
    exact absurd hfull (AffineSubspace.bot_ne_top ℝ (Fin n → ℝ) (Fin n → ℝ))
  · exact h

/-- The facet offset of a lattice hull is the integral minimum over the generators. -/
theorem facetOffset_latticeHull {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) (a : Fin n → ℤ) :
    ∃ v₀ ∈ V, facetOffset (latticeHull V) a = (zDot a v₀ : ℝ) ∧ (∀ v ∈ V, zDot a v₀ ≤ zDot a v) ∧
      ∀ x ∈ latticeHull V, (zDot a v₀ : ℝ) ≤ intDot a x := by
  obtain ⟨v₀, hv₀, hmin⟩ := V.exists_min_image (zDot a) hV
  have hlow : latticeHull V ⊆ {x | (zDot a v₀ : ℝ) ≤ intDotL a x} := by
    apply convexHull_min _ (convex_halfSpace_ge (intDotL a).isLinear _)
    rintro _ ⟨v, hv, rfl⟩
    show (zDot a v₀ : ℝ) ≤ intDot a (castPt v)
    rw [intDot_castPt]
    exact_mod_cast hmin v hv
  have hmem : castPt v₀ ∈ latticeHull V := subset_convexHull ℝ _ ⟨v₀, hv₀, rfl⟩
  refine ⟨v₀, hv₀, ?_, hmin, fun x hx => hlow hx⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨castPt v₀, hmem, intDot_castPt a v₀⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hlow hx

theorem IsPrimitive.ne_zero {a : Fin n → ℤ} (ha : IsPrimitive a) : a ≠ 0 := by
  rintro rfl
  have h2 := ha 2 (fun _ => dvd_zero 2)
  rw [Int.isUnit_iff] at h2
  omega

theorem IsPrimitive.exists_bezout {a : Fin n → ℤ} (ha : IsPrimitive a) :
    ∃ c : Fin n → ℤ, ∑ i, c i * a i = 1 := by
  have hdvd : ∀ i, Submodule.IsPrincipal.generator (Ideal.span (Set.range a)) ∣ a i := by
    intro i
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator]
    exact Ideal.subset_span ⟨i, rfl⟩
  have htop : Ideal.span (Set.range a) = ⊤ := by
    rw [← Ideal.span_singleton_generator (Ideal.span (Set.range a)), Ideal.span_singleton_eq_top]
    exact ha _ hdvd
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ (Set.range a) := by
    rw [Ideal.submodule_span_eq, htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

end Cayley382145

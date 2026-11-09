import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.Ring.Abs

namespace Nut8

variable {V : Type} [Fintype V]

def Cubic [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

def adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.mulVecLin (G.adjMatrix ℝ)

def Nut (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  2 ≤ Fintype.card V ∧ Module.finrank ℝ (LinearMap.ker (adjacency G)) = 1 ∧
    ∃ u : V → ℝ, u ≠ 0 ∧ adjacency G u = 0 ∧ ∀ v, u v ≠ 0

/-- The orbit relation is literally existence of an integer power of the automorphism. -/
def orbitSetoid (σ : Equiv.Perm V) : Setoid V :=
  ⟨σ.SameCycle, ⟨Equiv.Perm.SameCycle.refl σ, Equiv.Perm.SameCycle.symm, Equiv.Perm.SameCycle.trans⟩⟩

noncomputable def orbitFinset (σ : Equiv.Perm V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (σ.SameCycle v)

/-- One cyclic generator, exactly `l` orbits, equal orbit cardinalities. -/
def Circulant (l : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ σ : G ≃g G,
    Nat.card (Quotient (orbitSetoid σ.toEquiv)) = l ∧
    ∃ m : ℕ, ∀ v, (orbitFinset σ.toEquiv v).card = m

lemma mem_orbitFinset (σ : Equiv.Perm V) (v w : V) :
    w ∈ orbitFinset σ v ↔ σ.SameCycle v w := by
  classical
  simp [orbitFinset]

lemma cycleOn_orbit (σ : Equiv.Perm V) (v : V) :
    σ.IsCycleOn (orbitFinset σ v : Set V) := by
  constructor
  · refine ⟨?_, σ.injective.injOn, ?_⟩
    · intro w hw
      rw [Finset.mem_coe, mem_orbitFinset] at hw ⊢
      exact hw.apply_right
    · intro w hw
      refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
      rw [Finset.mem_coe, mem_orbitFinset] at hw ⊢
      exact hw.symm_apply_right
  · intro x hx y hy
    rw [Finset.mem_coe, mem_orbitFinset] at hx hy
    exact hx.symm.trans hy

/-- Equal finite orbit sizes force the generator's m-th power to be the identity. -/
theorem pow_eq_one_of_equal_orbits (σ : Equiv.Perm V) (m : ℕ)
    (h : ∀ v, (orbitFinset σ v).card = m) : σ ^ m = 1 := by
  ext v
  have hv : v ∈ orbitFinset σ v := (mem_orbitFinset σ v v).2 (.refl σ v)
  simpa [h v] using (cycleOn_orbit σ v).pow_card_apply hv

theorem circulant_semiregular (l : ℕ) (G : SimpleGraph V) (h : Circulant l G) :
    ∃ (σ : G ≃g G) (m : ℕ),
      Nat.card (Quotient (orbitSetoid σ.toEquiv)) = l ∧
      (∀ v, (orbitFinset σ.toEquiv v).card = m) ∧
      (σ.toEquiv : Equiv.Perm V) ^ m = 1 := by
  obtain ⟨σ, hc, m, hm⟩ := h
  exact ⟨σ, m, hc, hm, pow_eq_one_of_equal_orbits _ _ hm⟩

/-- Abstract one-dimensional stable-subspace bridge; no graph stability is assumed proved. -/
theorem stable_line_scalar {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) (hS : Module.finrank ℝ S = 1)
    (T : E →ₗ[ℝ] E) (stable : ∀ x ∈ S, T x ∈ S)
    (u : S) (hu : u ≠ 0) : ∃ e : ℝ, T (u : E) = e • (u : E) := by
  obtain ⟨e, he⟩ := exists_smul_eq_of_finrank_eq_one hS hu
    (⟨T u, stable u u.property⟩ : S)
  exact ⟨e, (congrArg Subtype.val he).symm⟩

/-- A scalar eigenvector transforms by the corresponding scalar power under iteration. -/
theorem iterate_scalar {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : E →ₗ[ℝ] E) (u : E) (e : ℝ) (h : T u = e • u) (n : ℕ) :
    (T ^ n) u = e ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ', mul_comm]

/-- The scalar on a real invariant line of positive finite period is a sign. -/
theorem scalar_is_sign {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : E →ₗ[ℝ] E) (u : E) (hu : u ≠ 0) (e : ℝ)
    (h : T u = e • u) (m : ℕ) (hm : m ≠ 0) (period : (T ^ m) u = u) :
    e = 1 ∨ e = -1 ∧ Even m := by
  have he : e ^ m = 1 := by
    have hsm : e ^ m • u = (1 : ℝ) • u := by
      rw [one_smul, ← iterate_scalar T u e h m, period]
    exact (smul_left_injective ℝ hu) hsm
  exact (pow_eq_one_iff_of_ne_zero hm).1 he

theorem stable_line_sign {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) (hS : Module.finrank ℝ S = 1)
    (T : E →ₗ[ℝ] E) (stable : ∀ x ∈ S, T x ∈ S)
    (u : S) (hu : u ≠ 0) (m : ℕ) (hm : m ≠ 0)
    (period : (T ^ m) (u : E) = (u : E)) :
    ∃ e : ℝ, T (u : E) = e • (u : E) ∧ (e = 1 ∨ e = -1 ∧ Even m) := by
  obtain ⟨e, he⟩ := stable_line_scalar S hS T stable u hu
  refine ⟨e, he, scalar_is_sign T u ?_ e he m hm period⟩
  exact fun h => hu (Subtype.ext h)

/-- Positive common orbit size is automatic on a nonempty vertex type. -/
theorem orbit_size_pos [Nonempty V] (σ : Equiv.Perm V) (m : ℕ)
    (h : ∀ v, (orbitFinset σ v).card = m) : 0 < m := by
  classical
  let v : V := Classical.choice inferInstance
  rw [← h v]
  exact Finset.card_pos.mpr ⟨v, (mem_orbitFinset σ v v).2 (.refl σ v)⟩

def pullback (σ : Equiv.Perm V) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u := u ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma adjacency_pullback (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : G ≃g G) (u : V → ℝ) :
    adjacency G (pullback σ.toEquiv u) = pullback σ.toEquiv (adjacency G u) := by
  ext v
  change (∑ w, G.adjMatrix ℝ v w * u (σ w)) =
    ∑ w, G.adjMatrix ℝ (σ v) w * u w
  calc
    _ = ∑ w, G.adjMatrix ℝ (σ v) (σ w) * u (σ w) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [SimpleGraph.adjMatrix_apply, σ.map_adj_iff]
    _ = _ := Equiv.sum_comp σ.toEquiv (fun w => G.adjMatrix ℝ (σ v) w * u w)

lemma kernel_stable (G : SimpleGraph V) [DecidableRel G.Adj] (σ : G ≃g G) :
    ∀ u ∈ LinearMap.ker (adjacency G),
      pullback σ.toEquiv u ∈ LinearMap.ker (adjacency G) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  rw [adjacency_pullback, hu, map_zero]

omit [Fintype V] in
lemma pullback_pow (σ : Equiv.Perm V) (n : ℕ) (u : V → ℝ) (v : V) :
    ((pullback σ ^ n) u) v = u ((σ ^ n) v) := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    change ((pullback σ ^ n) (pullback σ u)) v = _
    rw [ih]
    change u (σ ((σ ^ n) v)) = u ((σ ^ (n+1)) v)
    rw [pow_succ']
    rfl

/-- The graph kernel carries a sign character, with parity recorded in the negative case. -/
theorem nut_sign_character (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Nut G) (σ : G ≃g G) (m : ℕ) (hm : m ≠ 0)
    (hp : (σ.toEquiv : Equiv.Perm V) ^ m = 1) :
    ∃ (u : V → ℝ) (e : ℝ), u ≠ 0 ∧ adjacency G u = 0 ∧
      (∀ v, u v ≠ 0) ∧ (∀ v, u (σ v) = e * u v) ∧
      (e = 1 ∨ e = -1 ∧ Even m) := by
  obtain ⟨_, hd, u, hu, hker, hfull⟩ := hn
  let uk : LinearMap.ker (adjacency G) := ⟨u, hker⟩
  have huk : uk ≠ 0 := fun h => hu (congrArg Subtype.val h)
  have period : (pullback σ.toEquiv ^ m) u = u := by
    ext v
    rw [pullback_pow, hp]
    rfl
  obtain ⟨e, he, hs⟩ := stable_line_sign _ hd (pullback σ.toEquiv)
    (kernel_stable G σ) uk huk m hm period
  refine ⟨u, e, hu, hker, hfull, ?_, hs⟩
  intro v
  exact congrFun he v

theorem orbit_period_iff (σ : Equiv.Perm V) (v : V) (m : ℕ)
    (hm : (orbitFinset σ v).card = m) (n : ℕ) :
    (σ ^ n) v = v ↔ m ∣ n := by
  rw [← hm]
  exact (cycleOn_orbit σ v).pow_apply_eq ((mem_orbitFinset σ v v).2 (.refl σ v))

/-- Local orbit labelling, including the singleton case. -/
noncomputable def labelOrbit (σ : Equiv.Perm V) (v : V) :
    Fin (orbitFinset σ v).card ≃ {w // w ∈ orbitFinset σ v} := by
  classical
  let f : Fin (orbitFinset σ v).card → {w // w ∈ orbitFinset σ v} :=
    fun a => ⟨(σ ^ a.val) v, (mem_orbitFinset σ v _).2
      ⟨(a.val : ℤ), by simp⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hp : (σ ^ a.val) v = (σ ^ b.val) v := congrArg Subtype.val hab
    have hmod := ((cycleOn_orbit σ v).pow_apply_eq_pow_apply
      ((mem_orbitFinset σ v v).2 (.refl σ v))).1 hp
    apply Fin.ext
    exact hmod.eq_of_lt_of_lt a.isLt b.isLt
  · intro w
    obtain ⟨n, hn, he⟩ := (cycleOn_orbit σ v).exists_pow_eq
      ((mem_orbitFinset σ v v).2 (.refl σ v)) w.property
    exact ⟨⟨n, hn⟩, Subtype.ext he⟩

/-- Literal requested endpoint as a proposition only; no proof is supplied. -/
def Target : Prop := ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], ¬ (Cubic G ∧ Nut G ∧ Circulant 8 G)

end Nut8





import Cayley382145Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # MathDB 382145: optimal uniform-shift certificate from a separation argument

For finitely many affine rows `x ↦ ⟨α i, x⟩ - β i` whose uniform-shift set is nonempty and
bounded above with supremum `σ`, we construct `y ≥ 0`, `∑ y = 1`, `∑ y α = 0`,
`∑ y β = -σ` by strictly separating the compact convex image of the standard simplex from
the closed ray `{0} × (-∞, σ]` (geometric Hahn–Banach); weak duality gives equality.
A minimal-support optimal certificate has independent augmented rows. No LP duality
theorem is imported. -/

namespace Cayley382145

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Uniform shifts `s > 0` admitting a point with all row slacks at least `s`. -/
def shiftSet (α : ι → Fin n → ℝ) (β : ι → ℝ) : Set ℝ :=
  {s | 0 < s ∧ ∃ x, ∀ i, β i + s ≤ rdot (α i) x}

theorem weak_duality (α : ι → Fin n → ℝ) (β : ι → ℝ) {y : ι → ℝ} (hy0 : ∀ i, 0 ≤ y i)
    (hy1 : ∑ i, y i = 1) (hya : ∑ i, y i • α i = 0) {s : ℝ} (hs : s ∈ shiftSet α β) :
    s ≤ -∑ i, y i * β i := by
  obtain ⟨-, x, hx⟩ := hs
  have h1 : ∑ i, y i * (β i + s) ≤ ∑ i, y i * rdot (α i) x :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy0 i)
  rw [← rdot_sum, hya, rdot_zero_left] at h1
  have h2 : ∑ i, y i * (β i + s) = ∑ i, y i * β i + s := by
    rw [Finset.sum_congr rfl (fun i _ => mul_add (y i) (β i) s), Finset.sum_add_distrib,
      ← Finset.sum_mul, hy1, one_mul]
  linarith

/-- `y ↦ (∑ y α, -∑ y β)`. -/
noncomputable def dualMap (α : ι → Fin n → ℝ) (β : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ where
  toFun y := (∑ i, y i • α i, -∑ i, y i * β i)
  map_add' y z := by
    refine Prod.ext ?_ ?_
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Prod.fst_add]
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.snd_add, neg_add]
  map_smul' c y := by
    refine Prod.ext ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst, Finset.smul_sum,
        mul_smul]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_snd, Finset.mul_sum,
        mul_neg, mul_assoc]

theorem rdot_smul_right (c : ℝ) (u x : Fin n → ℝ) : rdot u (c • x) = c * rdot u x := by
  simp only [rdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The standard simplex in `ℝ^ι` (local definition). -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}

theorem isCompact_simplexSet : IsCompact (simplexSet ι) := by
  have hdef : simplexSet ι = {y : ι → ℝ | ∀ i, 0 ≤ y i} ∩ {y | ∑ i, y i = 1} := rfl
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1))
  · rw [hdef]
    apply IsClosed.inter
    · have hI : {y : ι → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y : ι → ℝ | 0 ≤ y i} := by
        ext y
        simp
      rw [hI]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  · rintro y ⟨h0, h1⟩
    refine ⟨fun i => h0 i, fun i => ?_⟩
    show y i ≤ 1
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

theorem convex_simplexSet : Convex ℝ (simplexSet ι) := by
  intro y hy z hz a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hb (hz.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hy.2, hz.2, mul_one, mul_one, hab]

theorem single_mem_simplexSet [DecidableEq ι] (i : ι) : (Pi.single i 1 : ι → ℝ) ∈ simplexSet ι := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Strong duality inequality via strict separation. -/
theorem exists_dual (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 ∧ ∑ i, y i • α i = 0 ∧
      -∑ i, y i * β i ≤ sSup (shiftSet α β) := by
  classical
  set σ := sSup (shiftSet α β) with hσ
  have hle : ∀ s ∈ shiftSet α β, s ≤ σ := fun s hs => le_csSup hbdd hs
  have hσpos : 0 < σ := by
    obtain ⟨s, hs⟩ := hne
    exact lt_of_lt_of_le hs.1 (hle s hs)
  by_contra hno
  push Not at hno
  have hDc : IsCompact (dualMap α β '' simplexSet ι) :=
    isCompact_simplexSet.image (dualMap α β).continuous_of_finiteDimensional
  have hDv : Convex ℝ (dualMap α β '' simplexSet ι) :=
    convex_simplexSet.linear_image (dualMap α β)
  have hRv : Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} := by
    intro p hp q hq a b ha hb hab
    refine ⟨?_, ?_⟩
    · simp [hp.1, hq.1]
    · have h1 := mul_le_mul_of_nonneg_left hp.2 ha
      have h2 := mul_le_mul_of_nonneg_left hq.2 hb
      have h3 : a * σ + b * σ = σ := by rw [← add_mul, hab, one_mul]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linarith
  have hRc : IsClosed {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} :=
    (isClosed_eq continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  have hdisj : Disjoint (dualMap α β '' simplexSet ι) {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨h1, h2⟩
    have h1' : ∑ i, y i • α i = 0 := h1
    have h2' : -∑ i, y i * β i ≤ σ := h2
    exact absurd h2' (not_le.mpr (hno y hy.1 hy.2 h1'))
  obtain ⟨f, u, v, hfD, huv, hfR⟩ := geometric_hahn_banach_compact_closed hDv hDc hRv hRc hdisj
  set lam := f ((0 : Fin n → ℝ), (1 : ℝ)) with hlamdef
  have hf0r : ∀ r : ℝ, f ((0 : Fin n → ℝ), r) = r * lam := by
    intro r
    have : ((0 : Fin n → ℝ), r) = r • ((0 : Fin n → ℝ), (1 : ℝ)) := by simp
    rw [this, map_smul, smul_eq_mul]
  have hR' : ∀ r ≤ σ, v < r * lam := fun r hr => by
    rw [← hf0r]
    exact hfR _ ⟨rfl, hr⟩
  have hlam : lam ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hr : -(|v| + 1) / lam < 0 := div_neg_of_neg_of_pos (by linarith [abs_nonneg v]) hpos
    have := hR' (-(|v| + 1) / lam) (by linarith)
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    linarith [neg_abs_le v]
  let g : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (f : (Fin n → ℝ) × ℝ →ₗ[ℝ] ℝ) ∘ₗ LinearMap.inl ℝ (Fin n → ℝ) ℝ
  have hg : ∀ x, g x = f (x, 0) := fun x => rfl
  let w : Fin n → ℝ := fun k => g (fun j => if k = j then 1 else 0)
  have hgw : ∀ x, g x = rdot x w := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ g x]
    simp only [rdot, smul_eq_mul, w]
  have hrd : ∀ (c : ℝ) (u' : Fin n → ℝ), rdot u' (c • w) = c * g u' := by
    intro c u'
    rw [rdot_smul_right, hgw]
  have hvert : ∀ i, dualMap α β (Pi.single i 1) = (α i, -β i) := by
    intro i
    refine Prod.ext ?_ ?_
    · show ∑ j, (Pi.single i 1 : ι → ℝ) j • α j = α i
      simp [Pi.single_apply]
    · show -∑ j, (Pi.single i 1 : ι → ℝ) j * β j = -β i
      simp [Pi.single_apply]
  have hfi : ∀ i, g (α i) - β i * lam < u := by
    intro i
    have h := hfD _ ⟨Pi.single i 1, single_mem_simplexSet i, rfl⟩
    rw [hvert] at h
    have hsplit : ((α i, -β i) : (Fin n → ℝ) × ℝ) = (α i, 0) + (0, -β i) := by simp
    rw [hsplit, map_add, hf0r, ← hg] at h
    linarith
  rcases hlam.lt_or_eq with hneg | hzero
  · have hu : u < σ * lam := lt_trans huv (hR' σ le_rfl)
    have hu0 : u < 0 := lt_trans hu (mul_neg_of_pos_of_neg hσpos hneg)
    have hmem : u / lam ∈ shiftSet α β := by
      refine ⟨div_pos_of_neg_of_neg hu0 hneg, lam⁻¹ • w, fun i => ?_⟩
      rw [hrd, ← mul_le_mul_right_of_neg hneg]
      have e1 : lam⁻¹ * g (α i) * lam = g (α i) := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hneg.ne, one_mul]
      have e2 : (β i + u / lam) * lam = β i * lam + u := by
        rw [add_mul, div_mul_cancel₀ u hneg.ne]
      rw [e1, e2]
      linarith [hfi i]
    have h1 := hle _ hmem
    have h2 : σ < u / lam := by
      rw [← mul_lt_mul_right_of_neg hneg, div_mul_cancel₀ u hneg.ne]
      exact hu
    linarith
  · have hv0 : v < 0 := by
      have := hR' σ le_rfl
      rw [hzero, mul_zero] at this
      exact this
    have hu0 : u < 0 := lt_trans huv hv0
    have hgi : ∀ i, g (α i) < u := fun i => by
      have := hfi i
      rw [hzero, mul_zero, sub_zero] at this
      exact this
    set B := ∑ i, |β i| with hB
    have hβB : ∀ i, β i ≤ B := fun i =>
      le_trans (le_abs_self _) (Finset.single_le_sum (fun j _ => abs_nonneg (β j)) (Finset.mem_univ i))
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg _
    set K := (σ + 1 + B) / (-u) with hK
    have hK0 : 0 ≤ K := div_nonneg (by linarith) (by linarith)
    have hKu : K * (-u) = σ + 1 + B := div_mul_cancel₀ _ (neg_pos.mpr hu0).ne'
    have hmem : σ + 1 ∈ shiftSet α β := by
      refine ⟨by linarith, (-K) • w, fun i => ?_⟩
      rw [hrd]
      have h1 : K * (-u) ≤ K * (-g (α i)) := mul_le_mul_of_nonneg_left (by linarith [hgi i]) hK0
      have h2 := hβB i
      linarith
    have := hle _ hmem
    linarith

/-- Optimal certificates. -/
def IsOptCert (α : ι → Fin n → ℝ) (β : ι → ℝ) (σ : ℝ) (y : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 ∧ ∑ i, y i • α i = 0 ∧ ∑ i, y i * β i = -σ

theorem exists_opt (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) : ∃ y, IsOptCert α β (sSup (shiftSet α β)) y := by
  obtain ⟨y, h0, h1, h2, h3⟩ := exists_dual α β hne hbdd
  refine ⟨y, h0, h1, h2, ?_⟩
  have h4 : sSup (shiftSet α β) ≤ -∑ i, y i * β i :=
    csSup_le hne fun s hs => weak_duality α β h0 h1 h2 hs
  linarith

/-- Ratio-test support reduction. -/
theorem shrink (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    {y : ι → ℝ} (hy : IsOptCert α β (sSup (shiftSet α β)) y) {z : ι → ℝ}
    (hzs : ∀ i, y i = 0 → z i = 0) (hza : ∑ i, z i • α i = 0) (hz1 : ∑ i, z i = 0) (hz0 : z ≠ 0)
    (hzb : ∑ i, z i * β i ≤ 0) :
    ∃ y', IsOptCert α β (sSup (shiftSet α β)) y' ∧
      (univ.filter (fun i => y' i ≠ 0)).card < (univ.filter (fun i => y i ≠ 0)).card := by
  obtain ⟨hy0, hy1, hya, hyb⟩ := hy
  have hpos : ∃ i, 0 < z i := by
    by_contra h
    push Not at h
    apply hz0
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => h j)).mp hz1 i (Finset.mem_univ i)
  have hPz : (univ.filter (fun i => 0 < z i)).Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := (univ.filter (fun i => 0 < z i)).exists_min_image
    (fun i => y i / z i) hPz
  have hzi₀ : 0 < z i₀ := (Finset.mem_filter.mp hi₀).2
  set ε := y i₀ / z i₀ with hεdef
  have hε : 0 ≤ ε := div_nonneg (hy0 i₀) hzi₀.le
  set y' : ι → ℝ := fun i => y i - ε * z i with hy'def
  have hy'0 : ∀ i, 0 ≤ y' i := by
    intro i
    rcases lt_or_ge 0 (z i) with hz | hz
    · have h1 := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz⟩)
      have h2 : ε * z i ≤ y i := (le_div_iff₀ hz).mp h1
      show 0 ≤ y i - ε * z i
      linarith
    · have h2 : ε * z i ≤ 0 := by nlinarith
      show 0 ≤ y i - ε * z i
      linarith [hy0 i]
  have hy'1 : ∑ i, y' i = 1 := by
    show ∑ i, (y i - ε * z i) = 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz1, mul_zero, sub_zero, hy1]
  have hy'a : ∑ i, y' i • α i = 0 := by
    show ∑ i, (y i - ε * z i) • α i = 0
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum, hza, smul_zero, sub_zero, hya]
  have hy'b : ∑ i, y' i * β i = ∑ i, y i * β i - ε * ∑ i, z i * β i := by
    show ∑ i, (y i - ε * z i) * β i = _
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum]
  have hwd : sSup (shiftSet α β) ≤ -∑ i, y' i * β i :=
    csSup_le hne fun s hs => weak_duality α β hy'0 hy'1 hy'a hs
  have hεzb : ε * ∑ i, z i * β i ≤ 0 := by nlinarith
  refine ⟨y', ⟨hy'0, hy'1, hy'a, by linarith⟩, ?_⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i₀, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h => ?_⟩
      have := hzs i₀ h
      linarith
    · rw [Finset.mem_filter, not_and, not_not]
      intro _
      show y i₀ - y i₀ / z i₀ * z i₀ = 0
      rw [div_mul_cancel₀ _ hzi₀.ne', sub_self]
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, fun h => hi.2 ?_⟩
    show y i - ε * z i = 0
    rw [h, hzs i h, mul_zero, sub_zero]

/-- A minimal-support optimal certificate with independent augmented rows. -/
theorem exists_min_cert (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) :
    ∃ y, IsOptCert α β (sSup (shiftSet α β)) y ∧
      ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0 := by
  classical
  have hex : ∃ m, ∃ y, IsOptCert α β (sSup (shiftSet α β)) y ∧
      (univ.filter (fun i => y i ≠ 0)).card = m := by
    obtain ⟨y, hy⟩ := exists_opt α β hne hbdd
    exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy, hcard⟩ := Nat.find_spec hex
  refine ⟨y, hy, fun z hzs hza hz1 => ?_⟩
  by_contra hz0
  have key : ∀ z' : ι → ℝ, (∀ i, y i = 0 → z' i = 0) → ∑ i, z' i • α i = 0 → ∑ i, z' i = 0 →
      z' ≠ 0 → ∑ i, z' i * β i ≤ 0 → False := by
    intro z' h1 h2 h3 h4 h5
    obtain ⟨y', hy', hlt⟩ := shrink α β hne hy h1 h2 h3 h4 h5
    have := Nat.find_min' hex ⟨y', hy', rfl⟩
    omega
  rcases le_total (∑ i, z i * β i) 0 with hb | hb
  · exact key z hzs hza hz1 hz0 hb
  · apply key (-z)
    · intro i hi
      simp [hzs i hi]
    · simp [neg_smul, Finset.sum_neg_distrib, hza]
    · simp [Finset.sum_neg_distrib, hz1]
    · exact neg_ne_zero.mpr hz0
    · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      linarith

/-- Independent augmented rows: the support has at most `n + 1` elements. -/
theorem card_support_le {y : ι → ℝ} {α : ι → Fin n → ℝ}
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0) :
    (univ.filter (fun i => y i ≠ 0)).card ≤ n + 1 := by
  classical
  set S := univ.filter (fun i => y i ≠ 0) with hS
  let u : S → (Fin n → ℝ) × ℝ := fun x => (α x, 1)
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    let z : ι → ℝ := fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
    have hz : ∀ F : ι → (Fin n → ℝ) × ℝ, ∑ i, z i • F i = ∑ x : S, g x • F x := by
      intro F
      rw [← Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by simp [z, hi]), ← Finset.sum_coe_sort S]
      exact Finset.sum_congr rfl fun x _ => by simp [z, x.2]
    have h0 : ∑ i, z i • ((α i, 1) : (Fin n → ℝ) × ℝ) = 0 := by
      rw [hz]
      exact hg
    have h1 : ∑ i, z i • α i = 0 := by
      have := congrArg Prod.fst h0
      simpa [Prod.fst_sum] using this
    have h2 : ∑ i, z i = 0 := by
      have := congrArg Prod.snd h0
      simpa [Prod.snd_sum] using this
    have hzs : ∀ i, y i = 0 → z i = 0 := by
      intro i hi
      have hiS : i ∉ S := by
        rw [hS, Finset.mem_filter]
        exact fun h => h.2 hi
      simp [z, hiS]
    have hzero := congrFun (hind z hzs h1 h2) x
    simpa [z, x.2] using hzero
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at this
  exact this

theorem sum_ite_mem_univ {M : Type*} [AddCommMonoid M] (J : Finset ι) (f : ι → M)
    [DecidablePred (· ∈ J)] : ∑ i, (if i ∈ J then f i else 0) = ∑ i ∈ J, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- A nonempty proper subset of the support has a nonzero row sum. -/
theorem sum_ne_zero_of_proper {y : ι → ℝ} {α : ι → Fin n → ℝ}
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0)
    (hy1 : ∑ i, y i = 1) (hya : ∑ i, y i • α i = 0)
    {J : Finset ι} (hJ : ∀ j ∈ J, y j ≠ 0) (hJne : J.Nonempty) {k : ι} (hk : y k ≠ 0)
    (hkJ : k ∉ J) : ∑ j ∈ J, α j ≠ 0 := by
  classical
  intro h
  let z : ι → ℝ := fun i => (if i ∈ J then 1 else 0) - (J.card : ℝ) * y i
  have hzs : ∀ i, y i = 0 → z i = 0 := by
    intro i hi
    have : i ∉ J := fun hiJ => hJ i hiJ hi
    simp [z, this, hi]
  have hza : ∑ i, z i • α i = 0 := by
    simp only [z, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, mul_smul]
    rw [← Finset.smul_sum, hya, smul_zero, sub_zero, sum_ite_mem_univ, h]
  have hz1 : ∑ i, z i = 0 := by
    simp only [z, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hy1, mul_one, sum_ite_mem_univ, Finset.sum_const, nsmul_eq_mul, mul_one,
      sub_self]
  have hk0 := congrFun (hind z hzs hza hz1) k
  have hzk : z k = -((J.card : ℝ) * y k) := by simp [z, hkJ]
  rw [hzk, Pi.zero_apply, neg_eq_zero] at hk0
  rcases mul_eq_zero.mp hk0 with h1 | h1
  · exact hJne.ne_empty (Finset.card_eq_zero.mp (by exact_mod_cast h1))
  · exact hk h1

end Cayley382145

import PolynomialConvexity.GapTransport
import PolynomialConvexity.Chambers
set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Finset

def gapAt {d : ℕ} (t : Fin d → ℝ) (i : Fin d) : ℝ :=
  t i - if h : i.val + 1 < d then t ⟨i.val+1,h⟩ else 0

theorem gapAt_tailSum {d : ℕ} (u : Fin d → ℝ) (i : Fin d) :
    gapAt (tailSum u) i = u i := by
  unfold gapAt
  split_ifs with h
  · let k : Fin d := ⟨i.val+1,h⟩
    have hs : univ.filter (i ≤ ·) = insert i (univ.filter (k ≤ ·)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      simp only [Fin.le_def, Fin.ext_iff, k]
      omega
    have hi : i ∉ univ.filter (k ≤ ·) := by simp [k, Fin.le_def]
    change tailSum u i - tailSum u k = u i
    rw [tailSum, hs, sum_insert hi]
    change u i + tailSum u k - tailSum u k = u i
    ring
  · have hs : univ.filter (i ≤ ·) = {i} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.le_def, Fin.ext_iff]
      have hj := j.isLt
      omega
    simp [tailSum, hs]

theorem gapAt_inverse {d : ℕ} (t : Fin d → ℝ) :
    gapAt t = (gapEquiv d).symm t := by
  obtain ⟨u, rfl⟩ := (gapEquiv d).surjective t
  rw [(gapEquiv d).symm_apply_apply]
  ext i
  rw [gapEquiv_apply, gapAt_tailSum]

theorem gap_positive_iff {d : ℕ} (u : Fin d → ℝ) :
    (∀ i, 0 < u i) ↔ tailSum u ∈ chamber (Equiv.refl _) := by
  constructor
  · intro hu
    exact ⟨tailSum_pos u hu, tailSum_strictAnti u hu⟩
  · rintro ⟨hp, ha⟩ i
    rw [← gapAt_tailSum u i]
    unfold gapAt
    split_ifs with h
    · exact sub_pos.mpr (ha (show i < (⟨i.val+1,h⟩ : Fin d) by simp [Fin.lt_def]))
    · simpa using hp i

theorem gap_preimage_chamber (d : ℕ) :
    (gapEquiv d) ⁻¹' chamber (Equiv.refl _) = Set.pi Set.univ (fun _ => Set.Ioi (0 : ℝ)) := by
  ext u
  simp only [Set.mem_preimage, gapEquiv_apply, ← gap_positive_iff, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioi]


def labelledGapEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  (gapEquiv d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) σ)

theorem labelledGapEquiv_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Fin d → ℝ) :
    labelledGapEquiv σ u = labelledGap σ u := by
  funext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) σ) (gapEquiv d u) (σ j) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp [labelledGap, gapEquiv_apply]

theorem labelledGap_measurePreserving {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    MeasurePreserving (labelledGapEquiv σ) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ) σ).comp
    (gap_measurePreserving d)

theorem labelledGap_preimage_chamber {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (labelledGapEquiv σ) ⁻¹' chamber σ =
      Set.pi Set.univ (fun _ => Set.Ioi (0 : ℝ)) := by
  ext u
  have heq : labelledGap σ u ∈ chamber σ ↔ tailSum u ∈ chamber (Equiv.refl _) := by
    constructor
    · rintro ⟨hp, ha⟩
      refine ⟨fun i => ?_, ?_⟩
      · simpa [labelledGap] using hp (σ i)
      · simpa [labelledGap, Function.comp_def] using ha
    · rintro ⟨hp, ha⟩
      exact ⟨fun i => hp (σ.symm i), by simpa [labelledGap, Function.comp_def] using ha⟩
  simp only [Set.mem_preimage, labelledGapEquiv_apply, heq, ← gap_positive_iff,
    Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioi]

end
end PolynomialConvexity

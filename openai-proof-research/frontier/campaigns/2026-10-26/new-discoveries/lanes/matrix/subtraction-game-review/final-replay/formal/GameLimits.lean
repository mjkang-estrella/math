import GameInvariant
import GameZigzag

open Finset Filter
open scoped Topology

namespace OddSubtraction

lemma eligible_full {S : Finset ℕ} {N : ℕ} (hN : ∀ k∈S, k≤N) :
    eligible S N=S := by
  ext k
  simp only [eligible, Finset.mem_filter]
  exact ⟨And.left, fun hk => ⟨hk,hN k hk⟩⟩

lemma limit_eq_half {S : Finset ℕ} {a : ℕ → ℝ} (hm : Model S a)
    (hne : S.Nonempty) {D : ℕ} (hD : ∀ k∈S, k≤D) {L : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) : L=1/2 := by
  have ht : (0:ℝ)<S.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hl := (ha.comp (tendsto_add_atTop_nat D)).const_mul (S.card:ℝ)
  have hs := tendsto_finsetSum S (fun k (_ : k∈S) =>
    ha.comp ((tendsto_sub_atTop_nat k).comp (tendsto_add_atTop_nat D)))
  have hr : Tendsto (fun n : ℕ => (S.card:ℝ)-∑ k∈S,a (n+D-k)) atTop
      (𝓝 ((S.card:ℝ)-∑ k∈S,L)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (S.card:ℝ)) atTop (𝓝 (S.card:ℝ))).sub hs
  have hsame : (fun n : ℕ => (S.card:ℝ)*a (n+D)) =
      (fun n : ℕ => (S.card:ℝ)-∑ k∈S,a (n+D-k)) := by
    funext n
    have h := hm.balance (n+D)
    rw [eligible_full (by intro k hk; have := hD k hk; omega)] at h
    exact h
  rw [← hsame] at hr
  have he := tendsto_nhds_unique hl hr
  simp only [Finset.sum_const, nsmul_eq_mul] at he
  nlinarith

lemma centered_tendsto_zero {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 (1/2:ℝ))) :
    Tendsto (centered a) atTop (𝓝 0) := by
  have h : Tendsto (fun n => (1:ℝ)-2*a n) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub (ha.const_mul 2) using 1; norm_num
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [centered, norm_mul] using h.norm

lemma window_tendsto_zero {S : Finset ℕ} {c : ℕ → ℝ} {D : ℕ}
    (hD : ∀ k∈S, k≤D) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => window S c (n+D)) atTop (𝓝 0) := by
  have hi (k : ℕ) (hk : k∈S) :
      Tendsto (fun n => prefixSum c (n+D)-prefixSum c (n+D-k)) atTop (𝓝 0) := by
    have he (n : ℕ) : prefixSum c (n+D)-prefixSum c (n+D-k)=
        ∑ j∈Finset.range k,c (n+(D-k+j)) := by
      have hbound := hD k hk
      have h := prefixSum_add c (n+D-k) k
      rw [show n+D-k+k=n+D by omega] at h
      rw [h, add_sub_cancel_left]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega
    have hh := tendsto_finsetSum (Finset.range k) (fun j _ =>
      hc.comp (tendsto_add_atTop_nat (D-k+j)))
    simpa only [Function.comp_def, ← he, Finset.sum_const_zero] using hh
  have h := tendsto_finsetSum S hi
  simpa only [window, Finset.sum_const_zero] using h

/-- Complete all-odd nonconvergence for every sequence satisfying the source recurrence. -/
theorem model_not_tendsto {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hne : S.Nonempty) (hodd : ∀ k∈S,k%2=1) (L : ℝ) :
    ¬ Tendsto a atTop (𝓝 L) := by
  intro ha
  let D := S.sup id
  have hD : ∀ k∈S,k≤D := by
    intro k hk
    exact Finset.le_sup (f := id) hk
  have hhalf := limit_eq_half hm hne hD ha
  rw [hhalf] at ha
  have hc := centered_tendsto_zero ha
  have hrec := centered_balance hm hodd
  have hf : ∀ n, (S.card:ℝ)*centered a (n+D)=∑ k∈S,centered a (n+D-k) := by
    intro n
    have h := hrec (n+D)
    rw [eligible_full (by intro k hk; have := hD k hk; omega)] at h
    exact h
  have hconst := window_constant hD hf
  have hw := window_tendsto_zero hD hc
  have hlim : Tendsto (fun _ : ℕ => window S (centered a) D) atTop (𝓝 0) :=
    hw.congr' (Filter.Eventually.of_forall hconst)
  have hz : window S (centered a) D=0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hp : (S.card:ℝ)≤window S (centered a) D := by
    rw [initial_window hD hrec]
    have h := Finset.sum_le_sum (fun k hk => odd_prefix_positive hm hodd k (hodd k hk))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have ht : (0:ℝ)<S.card := by exact_mod_cast Finset.card_pos.mpr hne
  linarith

end OddSubtraction

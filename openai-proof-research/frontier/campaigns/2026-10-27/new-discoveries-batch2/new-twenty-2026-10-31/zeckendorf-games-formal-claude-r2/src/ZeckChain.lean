/-
  Part (b) of MathDB 347063: the level chain.  After `j` levels the number of moves equals
  the counter plus `n/2 + n ∑_{i<j} 1/F_{2i+4}` up to `16 (j+1)`.
-/
import ZeckConst

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- The limiting density of the counter: `rho = 1/phi^2 = 2 - phi`. -/
noncomputable def rho : ℝ := 2 - phi

lemma rho_pos : 0 < rho := by
  unfold rho
  linarith [phi_lt_two]

lemma rho_le_one : rho ≤ 1 := by
  unfold rho
  linarith [phi_gt_one]

noncomputable def rr (n : ℕ) : ℝ := (Nat.fib n : ℝ) - rho * (Nat.fib (n + 2) : ℝ)

lemma rr_succ (n : ℕ) : rr (n + 1) = s * rr n := by
  have h1 : (Nat.fib (n + 2) : ℝ) = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_add_two
  have h2 : (Nat.fib (n + 1 + 2) : ℝ) = (Nat.fib (n + 1) : ℝ) + (Nat.fib (n + 2) : ℝ) := by
    exact_mod_cast Nat.fib_add_two
  have h := phi_sq
  unfold rr rho s
  rw [h2, h1]
  linear_combination ((Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ)) * h

lemma rr_abs_le (n : ℕ) : |rr n| ≤ 1 := by
  induction n with
  | zero =>
    have e : rr 0 = -rho := by simp [rr]
    rw [e, abs_neg, abs_of_pos rho_pos]
    exact rho_le_one
  | succ n ih =>
    rw [rr_succ, abs_mul]
    have h1 := abs_s_lt_one
    have h2 := abs_nonneg s
    have h3 := abs_nonneg (rr n)
    nlinarith

lemma d_approx (i : ℕ) : |(d i : ℝ) - rho * (F i : ℝ)| ≤ 2 := by
  rcases i with _ | n
  · have e : d 0 = 0 := by decide
    rw [e, F_zero]
    have h := rho_pos
    have h2 := rho_le_one
    rw [abs_le]
    constructor <;> push_cast <;> linarith
  · have hfn := rr_abs_le n
    rw [abs_le] at hfn
    obtain ⟨h1, h2⟩ := hfn
    have e1 : (F (n + 1) : ℝ) = (Nat.fib (n + 2) : ℝ) := by
      show (Nat.fib (n + 1 + 1) : ℝ) = _
      rfl
    unfold rr at h1 h2
    by_cases hev : (n + 1) % 2 = 0
    · have hd := d_even hev (by omega)
      have hd2 : (d (n + 1) : ℝ) + 1 = (Nat.fib n : ℝ) := by
        have h3 : d (n + 1) + 1 = Nat.fib n := by simpa using hd
        exact_mod_cast h3
      rw [e1, abs_le]
      constructor <;> nlinarith
    · have hd := d_odd (i := n + 1) (by omega)
      have hd2 : (d (n + 1) : ℝ) = (Nat.fib n : ℝ) := by
        have h3 : d (n + 1) = Nat.fib n := by simpa using hd
        exact_mod_cast h3
      rw [e1, abs_le]
      constructor <;> nlinarith

/-- The counter of an arbitrary position is `rho` times its value, up to the chip count. -/
lemma D_approx (a : Pos) : |(D a : ℝ) - rho * (val a : ℝ)| ≤ 2 * (chips a : ℝ) := by
  have e : (D a : ℝ) - rho * (val a : ℝ)
      = ∑ i ∈ a.support, (a i : ℝ) * ((d i : ℝ) - rho * (F i : ℝ)) := by
    unfold D val Finsupp.sum
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e2 : 2 * (chips a : ℝ) = ∑ i ∈ a.support, (a i : ℝ) * 2 := by
    unfold chips Finsupp.sum
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [e, e2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  have hc : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (d_approx i) hc

lemma w_le (i : ℕ) : w i ≤ (i : ℝ) + 3 := by
  have h1 : psi * s ^ i ≤ |psi * s ^ i| := le_abs_self _
  have h2 : |psi * s ^ i| ≤ psi := by
    rw [abs_mul, abs_of_pos psi_pos]
    nlinarith [abs_s_pow_le_one i, psi_pos]
  unfold w
  linarith [psi_lt_one]

lemma Phi_le_chips_mul (a : Pos) (T : ℕ) (h : ∀ i, T < i → a i = 0) :
    Phi a ≤ (chips a : ℝ) * ((T : ℝ) + 3) := by
  unfold Phi chips Finsupp.sum
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi' : i ≤ T := by
    by_contra hc
    rw [Finsupp.mem_support_iff] at hi
    exact hi (h i (by omega))
  have hw := w_le i
  have hi2 : (i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hi'
  have hc : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- The chain of READY states from the start of the game. -/
theorem chain (n J : ℕ) (hn : 1000 ≤ n) (hJ : F (2 * J + 2) ^ 2 ≤ n) :
    ∀ j, j ≤ J → ∃ z m h k e, Zk z (2 * j) ∧ h ≤ 2 ∧ Tr (start n) k e (B z (2 * j) m h) ∧
      |(k : ℝ) - e - ((n : ℝ) / 2 + n * Ssum j)| ≤ 16 * ((j : ℝ) + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨m, h, k, e, hh, hT, h1, h2⟩ := start_phase n (by omega)
    refine ⟨0, m, h, k, e, Zk_zero' _, hh, ?_, ?_⟩
    · simpa using hT
    · have h3 : (2 : ℝ) * e + n ≤ 2 * k := by exact_mod_cast h1
      have h4 : (2 : ℝ) * k ≤ 2 * e + n + 1 := by exact_mod_cast h2
      rw [Ssum_zero, abs_le]
      constructor <;> push_cast <;> linarith
  | succ j ih =>
    intro hj
    obtain ⟨z, m, h, k, e, hz, hh, hT, hQ⟩ := ih (by omega)
    have hval : val z + m * F (2 * j + 2) + h * F (2 * j + 4) = n := by
      have := hT.st.val_eq
      rw [val_B, val_start] at this
      exact this
    have hlt : val z < F (2 * j + 1) := hz.val_lt _ _
    have hF2 : F (2 * j + 4) ≤ 3 * F (2 * j + 2) := F_add_two_le (2 * j)
    have hF1 : F (2 * j + 1) ≤ F (2 * j + 2) := F_mono (by omega)
    have hFpos : 0 < F (2 * j + 2) := F_pos _
    have hmF : n ≤ (m + 7) * F (2 * j + 2) := by
      have h1 : h * F (2 * j + 4) ≤ 2 * (3 * F (2 * j + 2)) := Nat.mul_le_mul hh hF2
      nlinarith
    have hJ' : F (2 * j + 4) ≤ F (2 * J + 2) := F_mono (by omega)
    have hF42 : F (2 * j + 2) ≤ F (2 * j + 4) := F_mono (by omega)
    have hm24 : 24 ≤ m := by
      by_contra hc
      have hm23 : m + 7 ≤ 30 := by omega
      have h1 : n ≤ 30 * F (2 * j + 2) := le_trans hmF (Nat.mul_le_mul_right _ hm23)
      have h2 : F (2 * j + 2) * F (2 * j + 2) ≤ n := by
        calc F (2 * j + 2) * F (2 * j + 2) ≤ F (2 * J + 2) * F (2 * J + 2) :=
              Nat.mul_le_mul (le_trans hF42 hJ') (le_trans hF42 hJ')
          _ = F (2 * J + 2) ^ 2 := (pow_two _).symm
          _ ≤ n := hJ
      have h3 : F (2 * j + 2) ≤ 30 :=
        Nat.le_of_mul_le_mul_right (le_trans h2 h1) hFpos
      have h4 : n ≤ 900 := le_trans h1 (Nat.mul_le_mul_left 30 h3)
      omega
    obtain ⟨z', k', e', m', h', hz', hh', hT', hA, hB⟩ :=
      level_step (q := 2 * j) (by omega) hz m h hm24 hh
    have hTT := hT.trans hT'
    have hval' : val z' + m' * F (2 * j + 4) + h' * F (2 * j + 6) = n := by
      have := hTT.st.val_eq
      rw [val_B, val_start] at this
      exact this
    have hlt' : val z' < F (2 * j + 3) := hz'.val_lt _ _
    have hF2' : F (2 * j + 6) ≤ 3 * F (2 * j + 4) := F_add_two_le (2 * j + 2)
    have hF1' : F (2 * j + 3) ≤ F (2 * j + 4) := F_mono (by omega)
    have hFa : 0 < F (2 * j + 4) := F_pos _
    have hm'le : m' * F (2 * j + 4) ≤ n := by omega
    have hmF' : n ≤ (m' + 7) * F (2 * j + 4) := by
      have h1 : h' * F (2 * j + 6) ≤ 2 * (3 * F (2 * j + 4)) := Nat.mul_le_mul hh' hF2'
      nlinarith
    have hF0 : (0 : ℝ) < (F (2 * j + 4) : ℝ) := F_cast_pos _
    have hm1 : (m' : ℝ) * (F (2 * j + 4) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm'le
    have hm2 : (n : ℝ) ≤ ((m' : ℝ) + 7) * (F (2 * j + 4) : ℝ) := by exact_mod_cast hmF'
    have hd1 : (m' : ℝ) ≤ (n : ℝ) / (F (2 * j + 4) : ℝ) := by
      rw [le_div_iff₀ hF0]; exact hm1
    have hd2 : (n : ℝ) / (F (2 * j + 4) : ℝ) ≤ (m' : ℝ) + 7 := by
      rw [div_le_iff₀ hF0]; exact hm2
    have hSs : (n : ℝ) * Ssum (j + 1) = n * Ssum j + (n : ℝ) / (F (2 * j + 4) : ℝ) := by
      rw [Ssum_succ]
      unfold aT
      ring
    have hAr : (e' : ℝ) + m' ≤ k' + 3 := by exact_mod_cast hA
    have hBr : (k' : ℝ) ≤ e' + m' + 6 := by exact_mod_cast hB
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
    refine ⟨z', m', h', k + k', e + e', hz', hh', hTT, ?_⟩
    rw [abs_le] at hQ ⊢
    obtain ⟨hQ1, hQ2⟩ := hQ
    push_cast
    rw [hSs]
    constructor <;> linarith

end Zeck

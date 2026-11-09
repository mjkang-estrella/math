import SSA5.Bridge
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Conjecture 1 of Chu–Wang–Zhang (arXiv:2304.11403) fails for `m = 5`

There is a generating set `S5 ∈ S_5` whose code family `C_n(S5)` has strictly larger rate than
the code family `C_n(TC)` of all TC-dominant length-five sequences:
`|C_n(S5)| ≥ c₁ λⁿ` and `|C_n(TC)| ≤ c₂ μⁿ` with `λ = 1299/400 > μ = 649/200`.
-/

open Filter Topology

namespace SSA

open Classical

/-- The letters of a length-five word, in order. -/
def key (w : Word 5) : List Base := [w 0, w 1, w 2, w 3, w 4]

/-- The improved generating set for `m = 5` (512 words, stored in `sTree`). -/
def S5 : Set (Word 5) := {w | inS (key w) = true}

theorem word_eta (w : Word 5) : w = ![w 0, w 1, w 2, w 3, w 4] := by
  funext i; fin_cases i <;> rfl

theorem key_shift (w : Word 5) (c : Base) : key (shift w c) = [w 1, w 2, w 3, w 4, c] := rfl

theorem key_rc (w : Word 5) :
    key (rc w) = [(w 4).comp, (w 3).comp, (w 2).comp, (w 1).comp, (w 0).comp] := rfl

theorem comp_comp (b : Base) : b.comp.comp = b := by cases b <;> rfl

theorem rc_rc {m : ℕ} (w : Word m) : rc (rc w) = w := by
  funext i; simp [rc, comp_comp]

theorem check_tcCount : ∀ a b c d e : Base,
    tcCount ![a, b, c, d, e] = [a, b, c, d, e].countP isTCb := by
  decide +kernel

theorem check_genTC : ∀ a b c d e : Base,
    (inTC [a, b, c, d, e] = true → inTC [e.comp, d.comp, c.comp, b.comp, a.comp] = false) ∧
    (inTC [a, b, c, d, e] = true ∨ inTC [e.comp, d.comp, c.comp, b.comp, a.comp] = true) := by
  decide +kernel

theorem mem_TC (w : Word 5) : w ∈ TCDominant 5 ↔ inTC (key w) = true := by
  have h1 : tcCount w = (key w).countP isTCb := by
    rw [word_eta w]; exact check_tcCount (w 0) (w 1) (w 2) (w 3) (w 4)
  change ((5 : ℕ) : ℚ) / 2 < (tcCount w : ℚ) ↔ _
  simp only [inTC, h1, decide_eq_true_eq]
  generalize (key w).countP isTCb = k
  rw [show ((5 : ℕ) : ℚ) = 5 by norm_num, div_lt_iff₀ (by norm_num : (0 : ℚ) < 2)]
  constructor
  · intro h
    by_contra hk
    have : (k : ℚ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
    linarith
  · intro h
    have : (3 : ℚ) ≤ k := by exact_mod_cast h
    linarith

/-- Generic form of the generating-set property from a pairing oracle. -/
theorem isGeneratingSet_of (S : Set (Word 5)) (P : List Base → Bool)
    (hS : ∀ w, w ∈ S ↔ P (key w) = true)
    (hp : ∀ w : Word 5, (P (key w) = true → P (key (rc w)) = false) ∧
      (P (key w) = true ∨ P (key (rc w)) = true)) :
    IsGeneratingSet 5 S := by
  refine ⟨fun x hx hrc => ?_, fun S' hsub hS' => ?_⟩
  · rw [hS] at hx hrc
    rw [(hp x).1 hx] at hrc
    exact Bool.false_ne_true hrc
  · refine Set.Subset.antisymm (fun z hz => ?_) hsub
    by_contra hzS
    have hrz : rc z ∈ S := (hS _).2 ((hp z).2.resolve_left (fun h => hzS ((hS z).2 h)))
    exact hS' (rc z) (hsub hrz) (by rw [rc_rc]; exact hz)

/-- `S5` belongs to the family `S_5` of Definition 4. -/
theorem S5_isGeneratingSet : IsGeneratingSet 5 S5 :=
  isGeneratingSet_of S5 inS (fun _ => Iff.rfl) fun w => by
    rw [key_rc]; exact check_gen (w 0) (w 1) (w 2) (w 3) (w 4)

/-- The TC-dominant set is itself a generating set for `m = 5`. -/
theorem TC_isGeneratingSet : IsGeneratingSet 5 (TCDominant 5) :=
  isGeneratingSet_of (TCDominant 5) inTC mem_TC fun w => by
    rw [key_rc]; exact check_genTC (w 0) (w 1) (w 2) (w 3) (w 4)

theorem lw_mem {n : ℕ} (S : Set (Word 5)) (h : 5 ≤ n) {x : Fin n → Base}
    (hx : x ∈ code 5 n S) : lw x h ∈ S := by
  simp only [code, Finset.mem_filter] at hx
  exact hx.2 _ _

theorem sum_base {M : Type*} [AddCommMonoid M] (f : Base → M) :
    ∑ c : Base, f c = f .A + f .C + f .G + f .T := by
  rw [show (Finset.univ : Finset Base) = {Base.A, Base.C, Base.G, Base.T} by decide]
  simp [Finset.sum_insert, add_assoc]

theorem ite_vS (w : Word 5) (c : Base) {inst : Decidable (shift w c ∈ S5)} :
    @ite _ (shift w c ∈ S5) inst (vS [w 1, w 2, w 3, w 4, c]) 0 = vS [w 1, w 2, w 3, w 4, c] := by
  split_ifs with hc
  · rfl
  · have : inS (key (shift w c)) = false := by
      cases hh : inS (key (shift w c))
      · rfl
      · exact absurd hh hc
    rw [key_shift] at this
    simp [vS, this]

theorem ite_uT (w : Word 5) (c : Base) {inst : Decidable (shift w c ∈ TCDominant 5)} :
    @ite _ (shift w c ∈ TCDominant 5) inst (uT [w 1, w 2, w 3, w 4, c]) 0 =
      uT [w 1, w 2, w 3, w 4, c] := by
  split_ifs with hc
  · rfl
  · have : inTC (key (shift w c)) = false := by
      cases hh : inTC (key (shift w c))
      · rfl
      · exact absurd ((mem_TC _).2 hh) hc
    rw [key_shift] at this
    simp [uT, this]

/-! ## Lower bound for `C_n(S5)` -/

/-- Weighted count `Ψ(n) = ∑_{x ∈ C_n(S5)} v(last window of x)`. -/
noncomputable def Psi (n : ℕ) (h : 5 ≤ n) : ℕ := ∑ x ∈ code 5 n S5, vS (key (lw x h))

theorem Psi_step (n : ℕ) (h : 5 ≤ n) : lamNum * Psi n h ≤ lamDen * Psi (n + 1) (by omega) := by
  unfold Psi
  rw [sum_code_succ S5 h (fun w => vS (key w)), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have hmem : inS (key (lw y h)) = true := lw_mem S5 h hy
  simp only [sum_base, key_shift, ite_vS]
  exact check_lower _ _ _ _ _ hmem

theorem Psi_iter (k : ℕ) :
    lamNum ^ k * Psi 5 le_rfl ≤ lamDen ^ k * Psi (5 + k) (by omega) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := Psi_step (5 + k) (by omega)
    calc lamNum ^ (k + 1) * Psi 5 le_rfl = lamNum * (lamNum ^ k * Psi 5 le_rfl) := by ring
      _ ≤ lamNum * (lamDen ^ k * Psi (5 + k) (by omega)) := Nat.mul_le_mul_left _ ih
      _ = lamDen ^ k * (lamNum * Psi (5 + k) (by omega)) := by ring
      _ ≤ lamDen ^ k * (lamDen * Psi (5 + k + 1) (by omega)) := Nat.mul_le_mul_left _ hs
      _ = lamDen ^ (k + 1) * Psi (5 + (k + 1)) (by omega) := by ring

theorem Psi_le (n : ℕ) (h : 5 ≤ n) : Psi n h ≤ (code 5 n S5).card * vMax := by
  unfold Psi
  have := Finset.sum_le_card_nsmul (code 5 n S5) (fun x => vS (key (lw x h))) vMax
    (fun x _ => (check_bounds _ _ _ _ _).1)
  simpa using this

/-- The witness sequence `TTACA`. -/
def x0 : Fin 5 → Base := ![.T, .T, .A, .C, .A]

theorem Psi_five_ge : vS [.T, .T, .A, .C, .A] ≤ Psi 5 le_rfl := by
  have hw : ∀ (i : ℕ) (hi : i + 5 ≤ 5), window 5 x0 i hi = x0 := by
    intro i hi
    obtain rfl : i = 0 := by omega
    funext j; simp [window]
  have hx0 : x0 ∈ code 5 5 S5 := by
    simp only [code, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    rw [hw i hi]
    exact check_witness.1
  unfold Psi
  have := Finset.single_le_sum (f := fun x => vS (key (lw x le_rfl)))
    (fun _ _ => Nat.zero_le _) hx0
  have hl : lw x0 le_rfl = x0 := hw 0 (by omega)
  simp only [hl] at this
  exact this

theorem lower_bound (k : ℕ) :
    lamNum ^ k * vS [.T, .T, .A, .C, .A] ≤
      lamDen ^ k * vMax * (code 5 (5 + k) S5).card := by
  calc lamNum ^ k * vS [.T, .T, .A, .C, .A] ≤ lamNum ^ k * Psi 5 le_rfl :=
        Nat.mul_le_mul_left _ Psi_five_ge
    _ ≤ lamDen ^ k * Psi (5 + k) (by omega) := Psi_iter k
    _ ≤ lamDen ^ k * ((code 5 (5 + k) S5).card * vMax) := Nat.mul_le_mul_left _ (Psi_le _ _)
    _ = lamDen ^ k * vMax * (code 5 (5 + k) S5).card := by ring

/-! ## Upper bound for `C_n(TC)` -/

/-- Weighted count `Φ(n) = ∑_{x ∈ C_n(TC)} u(last window of x)`. -/
noncomputable def Phi (n : ℕ) (h : 5 ≤ n) : ℕ :=
  ∑ x ∈ code 5 n (TCDominant 5), uT (key (lw x h))

theorem Phi_step (n : ℕ) (h : 5 ≤ n) : muDen * Phi (n + 1) (by omega) ≤ muNum * Phi n h := by
  unfold Phi
  rw [sum_code_succ (TCDominant 5) h (fun w => uT (key w)), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have hmem : inTC (key (lw y h)) = true := (mem_TC _).1 (lw_mem _ h hy)
  simp only [sum_base, key_shift, ite_uT]
  exact check_upper _ _ _ _ _ hmem

theorem Phi_iter (k : ℕ) :
    muDen ^ k * Phi (5 + k) (by omega) ≤ muNum ^ k * Phi 5 le_rfl := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := Phi_step (5 + k) (by omega)
    calc muDen ^ (k + 1) * Phi (5 + (k + 1)) (by omega)
        = muDen ^ k * (muDen * Phi (5 + k + 1) (by omega)) := by ring
      _ ≤ muDen ^ k * (muNum * Phi (5 + k) (by omega)) := Nat.mul_le_mul_left _ hs
      _ = muNum * (muDen ^ k * Phi (5 + k) (by omega)) := by ring
      _ ≤ muNum * (muNum ^ k * Phi 5 le_rfl) := Nat.mul_le_mul_left _ ih
      _ = muNum ^ (k + 1) * Phi 5 le_rfl := by ring

theorem Phi_ge (n : ℕ) (h : 5 ≤ n) : (code 5 n (TCDominant 5)).card * uMin ≤ Phi n h := by
  unfold Phi
  have := Finset.card_nsmul_le_sum (code 5 n (TCDominant 5)) (fun x => uT (key (lw x h))) uMin
    (fun x hx => (check_bounds _ _ _ _ _).2.2 ((mem_TC _).1 (lw_mem _ h hx)))
  simpa using this

theorem card_base : Fintype.card Base = 4 := rfl

theorem Phi_five_le : Phi 5 le_rfl ≤ 1024 * uMax := by
  unfold Phi
  have h1 := Finset.sum_le_card_nsmul (code 5 5 (TCDominant 5)) (fun x => uT (key (lw x le_rfl)))
    uMax (fun x _ => (check_bounds _ _ _ _ _).2.1)
  have h2 : (code 5 5 (TCDominant 5)).card ≤ 1024 := by
    have := Finset.card_le_univ (code 5 5 (TCDominant 5))
    simpa [Fintype.card_fun, card_base] using this
  simp only [smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right _ h2)

theorem upper_bound (k : ℕ) :
    uMin * muDen ^ k * (code 5 (5 + k) (TCDominant 5)).card ≤ muNum ^ k * (1024 * uMax) := by
  calc uMin * muDen ^ k * (code 5 (5 + k) (TCDominant 5)).card
      = muDen ^ k * ((code 5 (5 + k) (TCDominant 5)).card * uMin) := by ring
    _ ≤ muDen ^ k * Phi (5 + k) (by omega) := Nat.mul_le_mul_left _ (Phi_ge _ _)
    _ ≤ muNum ^ k * Phi 5 le_rfl := Phi_iter k
    _ ≤ muNum ^ k * (1024 * uMax) := Nat.mul_le_mul_left _ Phi_five_le

end SSA

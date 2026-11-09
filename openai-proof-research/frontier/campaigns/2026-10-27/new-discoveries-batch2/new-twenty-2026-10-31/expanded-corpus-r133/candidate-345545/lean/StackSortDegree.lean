/-
  UNCOMPILED DRAFT (lane expanded-corpus-r133; Lean not run here by memory restriction).
  NOT a certificate. Contains `sorry` placeholders, each marking a lemma whose ordinary proof
  is in ../CANDIDATE.md §3. Root / Sol worker: compile, replace each `sorry`, audit axioms.

  Target: refutation of Defant–Propp Conjecture 4.4 (arXiv:2002.07144v4):
    lim_{n→∞} deg(s : S_n → S_n)^{1/n} ∉ (1.68, 1.73).
  deg is Definition 1.1 of the source: deg f = (1/|X|) Σ_{x∈X} |f⁻¹(f x)|.
-/
import Mathlib

open Filter Topology BigOperators

namespace StackSortDegree

/-! ### West's stack-sorting map (source §2.3): s(L m R) = s(L) s(R) m, m the maximum. -/

/-- Literal recursive definition on lists of naturals (distinct entries in our use). -/
def stackSort : List ℕ → List ℕ
  | [] => []
  | (x :: xs) =>
    let l := x :: xs
    let m := l.foldr max 0
    let L := l.takeWhile (· ≠ m)
    let R := (l.dropWhile (· ≠ m)).drop 1
    stackSort L ++ stackSort R ++ [m]
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals sorry -- length (takeWhile) < length, length (drop 1 (dropWhile)) < length: routine

/-- One-line notation of σ ∈ S_n as a list of naturals (values 0..n-1). -/
def oneLine {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (fun i => (σ i : ℕ))

/-- The stack-sorting map on S_n, viewed through the injective one-line embedding
    S_n ↪ List ℕ. Fibers of `sList` coincide with fibers of s : S_n → S_n because
    `oneLine` is injective and s(S_n) ⊆ S_n (source §2.3). -/
def sList {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := stackSort (oneLine σ)

/-- Source Definition 1.1 for f = s : S_n → S_n. -/
noncomputable def deg (n : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n),
      ((Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => sList τ = sList σ)).card : ℝ))
    / (Nat.factorial n : ℝ)

/-- Pair count P_n = #{(σ,τ) : s σ = s τ}; deg n = P n / n!. -/
def P (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun st : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      sList st.1 = sList st.2)).card

theorem deg_eq (n : ℕ) : deg n = (P n : ℝ) / (Nat.factorial n : ℝ) := by
  sorry -- Σ_σ |fiber(σ)| = #pairs; Finset.card_filter / sum_comm

theorem P_pos (n : ℕ) : 0 < P n := by
  sorry -- (σ, σ) is always a pair

/-! ### Source inequality (1), case m = n: d_a^2 ≤ (2a+1) d_{2a+1}.
  Combinatorial form: C(2a, a) · P a ^ 2 ≤ P (2a+1)
  (injection (π,π',σ,σ',A) ↦ (π̃ N σ̃, π̃' N σ̃'), source proof of Theorem 2.5). -/
theorem doubling_comb (a : ℕ) : Nat.choose (2 * a) a * P a ^ 2 ≤ P (2 * a + 1) := by
  sorry -- requires standardization lemmas for stackSort on value-shifted lists

theorem doubling (a : ℕ) : deg a ^ 2 ≤ (2 * a + 1 : ℝ) * deg (2 * a + 1) := by
  sorry -- from doubling_comb and deg_eq: (2a+1)!/(a!)^2 = (2a+1) C(2a,a)

/-! ### Doubling ⇒ lower bound on the limit (ordinary proof: CANDIDATE.md §3.2). -/
theorem limit_ge_of_doubling (a : ℕ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => (deg n) ^ ((1 : ℝ) / n)) atTop (𝓝 L)) :
    (deg a / (4 * (a + 1))) ^ ((1 : ℝ) / (a + 1)) ≤ L := by
  sorry -- iterate `doubling` along a_k + 1 = 2^k (a+1); geometric-series bound on the losses

/-! ### Exact pair count via the closure–hook-length formula and block recursion (§3.3).
  Integer DP (labelled counts). `Ii r s m` = m! · I(r,s,m), etc. -/

def mu : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

/-- Fuel-indexed mutual recursion is awkward in Lean; a production version should tabulate
    bottom-up in m. This draft states the recursion abstractly. -/
structure DPTable where
  I : ℕ → ℕ → ℕ → ℕ
  X : ℕ → ℕ → ℕ → ℕ
  Y : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- Recursion equations satisfied by the DP (see scripts/stack_pairs_int.py). -/
def DPTable.Valid (T : DPTable) : Prop :=
  (∀ r s m, (r < 1 ∨ s < 1 ∨ m < 1 ∨ r > m ∨ s > m) → T.I r s m = 0) ∧
  T.I 1 1 1 = 1 ∧
  (∀ r s m, 1 ≤ r → 1 ≤ s → r ≤ m + 2 → s ≤ m + 2 → 1 ≤ m →
    T.I r s (m + 1) =
      ∑ t ∈ Finset.range 3, ∑ u ∈ Finset.range 3,
        if t = 0 ∧ u = 0 then 0 else
          mu t * mu u * T.Y (min r (r - 1 + t)) (min s (s - 1 + u)) (r - 1 + t) (s - 1 + u) m) ∧
  (∀ R S M, T.X R S M =
      if M = 0 then (if R = 0 ∧ S = 0 then 1 else 0)
      else ∑ m₁ ∈ Finset.Icc 1 M, ∑ r₁ ∈ Finset.Icc 1 R, ∑ s₁ ∈ Finset.Icc 1 S,
        Nat.choose M m₁ * T.I r₁ s₁ m₁ * T.X (R - r₁) (S - s₁) (M - m₁)) ∧
  (∀ a b R S M, T.Y a b R S M =
      if M = 0 then (if R = 0 ∧ S = 0 then 1 else 0)
      else T.I R S M + ∑ m₁ ∈ Finset.Ico 1 M, ∑ r₁ ∈ Finset.Icc 1 R, ∑ s₁ ∈ Finset.Icc 1 S,
        if a ≤ r₁ ∨ b ≤ s₁ then Nat.choose M m₁ * T.I r₁ s₁ m₁ * T.X (R - r₁) (S - s₁) (M - m₁)
        else 0)

/-- MAIN COMBINATORIAL LEMMA (ordinary proof in CANDIDATE.md §3.3 (a)–(e)):
    decreasing-tree bijection, closure lemma, forest hook-length formula, block recursion. -/
theorem P_eq_dp (T : DPTable) (hT : T.Valid) (n : ℕ) (hn : 1 ≤ n) : P n = T.I 1 1 n := by
  sorry

/-- Certificate value (scripts/stack_pairs_int.py; outputs/stack_pairs_P_1_82.json). -/
def P50 : ℕ := 9385583269767512161193412991288095407166959926264841564653575816719248830768416

theorem dp_50 (T : DPTable) (hT : T.Valid) : T.I 1 1 50 = P50 := by
  sorry -- kernel evaluation of a tabulated DP; too heavy as stated: see CANDIDATE.md §5,
        -- recommended split: DP to n = 20 + elementary recursion
        -- G_n ≥ 4 G_{n-1} + Σ_{i=1}^{n-2} C(n-1,i) G_i G_{n-1-i} to n = 300.

/-- Exact integer inequality: P50 · 100^51 > 4 · 51 · 50! · 173^51 (checked in Python). -/
theorem cert_ineq : 4 * 51 * Nat.factorial 50 * 173 ^ 51 < P50 * 100 ^ 51 := by
  decide -- or norm_num [Nat.factorial]; pure ℕ arithmetic on ~100-digit numbers

/-- Existence of a valid DP table (bottom-up construction). -/
theorem exists_table : ∃ T : DPTable, T.Valid := by
  sorry

/-! ### Endpoint. -/
theorem defant_propp_conjecture_4_4_false :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (deg n) ^ ((1 : ℝ) / n)) atTop (𝓝 L) ∧
        (1.68 : ℝ) < L ∧ L < 1.73 := by
  rintro ⟨L, hL, -, hlt⟩
  obtain ⟨T, hT⟩ := exists_table
  have h50 : P 50 = P50 := (P_eq_dp T hT 50 (by norm_num)).trans (dp_50 T hT)
  have hge := limit_ge_of_doubling 50 L hL
  -- (deg 50 / 204)^(1/51) > 1.73 from cert_ineq, deg_eq, h50
  have hcert : (1.73 : ℝ) < (deg 50 / (4 * (50 + 1))) ^ ((1 : ℝ) / (50 + 1)) := by
    sorry -- rpow monotonicity + cert_ineq cast to ℝ
  linarith

end StackSortDegree

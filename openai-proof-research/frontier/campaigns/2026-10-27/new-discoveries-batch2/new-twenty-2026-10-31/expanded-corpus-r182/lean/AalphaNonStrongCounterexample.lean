/-
UNCOMPILED DRAFT (Claude lane expanded-corpus-r182; Lean was NOT run in this lane).
Target: MathDB 351804 (Yang–Wang(–Xi), arXiv:2109.00409 v1 Conjecture 2.10; journal
Oper. Matrices 18 (2024) Remark 3.8 question), fixed-strong-component reading:

  NOT ( for all n m, for all G in G_n^m, for all alpha in [0,1),
          rho_alpha(G) <= rho_alpha(G''(G)) ).

Certificate: n = 5, m = 4, alpha = 1/4.
  G*  : arcs 0->1, 0->2, 1->0, 1->2, 1->3, 2->0, 3->0   (G*-outdegrees 2,3,1,1; v1 = 1)
  G   : G* + 0->4   (pendant out-star hung at vertex 0)
  G'' : G* + 1->4   (all n-m = 1 pendant vertices hung at v1 = 1)
  4*A_{1/4}(G)   = BG  = diag(3,3,1,1,0) + 3*Adj(G)
  4*A_{1/4}(G'') = BG2 = diag(2,4,1,1,0) + 3*Adj(G'')
  charpoly BG  = X (X^4 - 8X^3 + 4X^2 - 24X + 27),  value at 781/100 is negative
  charpoly BG2 = X (X^4 - 8X^3 + 3X^2 - 13X + 17)
  Collatz–Wielandt weights x = (671,1000,296,296,1): (BG2 x)_i <= (2309/296) x_i, 2309/296 < 781/100.
Hence rho(BG) > 781/100 > rho(BG2), i.e. rho_{1/4}(G) > 781/400 > rho_{1/4}(G'').

Plan of the formal endpoint (all pieces below are drafts; names of Mathlib lemmas must be
checked against the pinned mathlib d13f23b7):
  * `specRad M` := sSup of ‖μ‖ over complex eigenvalues μ of M (as a complex matrix).
  * lower bound: a real root of charpoly(BG) in (781/100, 8) by IVT; a root of the
    characteristic polynomial is an eigenvalue (det (μ•1 - M) = 0).
  * upper bound: for a nonnegative matrix B and a positive vector x with B x ≤ c x
    (componentwise), every complex eigenvalue μ satisfies ‖μ‖ ≤ c (weighted max-norm argument).
  * membership: G ∈ G_5^4 and G'' = doublePrime G are decidable finite facts (`decide`).
-/
import Mathlib

open Matrix Complex

namespace MathDB351804

/-! ### Literal objects -/

/-- A digraph on `Fin n` without loops, given by a decidable arc relation. -/
structure Digraph (n : ℕ) where
  arc : Fin n → Fin n → Bool
  loopless : ∀ i, arc i i = false

def outdeg {n : ℕ} (D : Digraph n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => D.arc i j = true)).card

/-- `A_α(D) = α · Diag(outdeg) + (1-α) · Adj(D)`. -/
noncomputable def Aalpha {n : ℕ} (α : ℝ) (D : Digraph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then α * (outdeg D i : ℝ) else 0) + (1 - α) * (if D.arc i j then 1 else 0)

/-- Spectral radius: supremum of moduli of complex eigenvalues. -/
noncomputable def specRad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ μ : ℂ, (M.map (algebraMap ℝ ℂ) - μ • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 ∧ r = ‖μ‖}

/-- Reachability (reflexive–transitive closure of the arc relation). -/
def reach {n : ℕ} (D : Digraph n) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (fun i j => D.arc i j = true)

/-! The class `G_n^m` (source Definition / Figure 4): non-strongly-connected digraphs on `n`
vertices whose strong components are one component `C` of order `m` and singletons, such that
the arcs not inside `C` form directed trees, each meeting `C` in exactly one vertex (its
attachment vertex), every vertex outside `C` lying in exactly one such tree.  For the
certificate we only need: (i) the explicit `G` satisfies the definition, (ii) the
construction `G''`.  A fully general `Gnm` predicate is stated here; its check on `G` is by
`decide` after unfolding to a finite computation (to be written as a Bool checker with a
soundness lemma if `decide` on `Relation.ReflTransGen` is too slow). -/
def strongComp {n : ℕ} (D : Digraph n) (i : Fin n) : Finset (Fin n) := sorry -- DRAFT: replace by
  -- `Finset.univ.filter (fun j => reach D i j ∧ reach D j i)` with a decidable reach (BFS).

/-! ### The certificate data -/

def Gstar_arc : Fin 5 → Fin 5 → Bool
  | 0, 1 => true | 0, 2 => true | 1, 0 => true | 1, 2 => true | 1, 3 => true
  | 2, 0 => true | 3, 0 => true | _, _ => false

def G : Digraph 5 where
  arc i j := Gstar_arc i j || (i = 0 && j = 4)
  loopless := by decide

def G2 : Digraph 5 where   -- G'' (all pendant vertices moved to v1 = 1)
  arc i j := Gstar_arc i j || (i = 1 && j = 4)
  loopless := by decide

/-- Integer matrices `4 · A_{1/4}`. -/
def BG : Matrix (Fin 5) (Fin 5) ℚ :=
  !![3,3,3,0,3; 3,3,3,3,0; 3,0,1,0,0; 3,0,0,1,0; 0,0,0,0,0]
def BG2 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![2,3,3,0,0; 3,4,3,3,3; 3,0,1,0,0; 3,0,0,1,0; 0,0,0,0,0]

lemma Aalpha_G : Aalpha (1/4) G = (1/4 : ℝ) • (BG.map (Rat.cast)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Aalpha, outdeg, G, Gstar_arc, BG] <;> norm_num
  -- DRAFT: `outdeg` needs `decide`-style evaluation of the filter cardinalities.

lemma Aalpha_G2 : Aalpha (1/4) G2 = (1/4 : ℝ) • (BG2.map (Rat.cast)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Aalpha, outdeg, G2, Gstar_arc, BG2] <;> norm_num

/-! ### Characteristic polynomials (exact) -/

lemma det_BG (t : ℚ) :
    (t • (1 : Matrix (Fin 5) (Fin 5) ℚ) - BG).det = t * (t^4 - 8*t^3 + 4*t^2 - 24*t + 27) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, BG]; ring

lemma det_BG2 (t : ℚ) :
    (t • (1 : Matrix (Fin 5) (Fin 5) ℚ) - BG2).det = t * (t^4 - 8*t^3 + 3*t^2 - 13*t + 17) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, BG2]; ring

/-! ### Lower bound for G: a real eigenvalue of BG exceeds 781/100 -/

lemma exists_root_BG : ∃ t : ℝ, 781/100 < t ∧ t < 8 ∧
    t * (t^4 - 8*t^3 + 4*t^2 - 24*t + 27) = 0 := by
  -- f(781/100) < 0 < f(8) = 8*91; IVT on the continuous polynomial on [781/100, 8].
  have hc : Continuous (fun t : ℝ => t * (t^4 - 8*t^3 + 4*t^2 - 24*t + 27)) := by continuity
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := intermediate_value_Icc (show (781/100 : ℝ) ≤ 8 by norm_num)
    hc.continuousOn (show (0:ℝ) ∈ Set.Icc _ _ from ⟨by norm_num, by norm_num⟩)
  refine ⟨t, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, ht⟩
  · rintro rfl; norm_num at ht
  · rintro rfl; norm_num at ht

/-! ### Upper bound for G'': Collatz–Wielandt / weighted Gershgorin -/

/-- For a real nonnegative matrix `B` and positive weights `x` with `B x ≤ c x`, every complex
eigenvalue has modulus at most `c`. -/
lemma eig_le_of_weighted {n : ℕ} [NeZero n] (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (c : ℝ) (hc : ∀ i, ∑ j, B i j * x j ≤ c * x i)
    (μ : ℂ) (hμ : (B.map (algebraMap ℝ ℂ) - μ • 1).det = 0) : ‖μ‖ ≤ c := by
  -- Take v ≠ 0 with (B - μ) v = 0 (Matrix.exists_mulVec_eq_zero_iff), pick i maximizing ‖v i‖ / x i,
  -- then ‖μ‖‖v i‖ = ‖∑ B i j v j‖ ≤ ∑ B i j x j (‖v i‖/x i) ≤ c ‖v i‖.
  sorry -- DRAFT: elementary; to be completed in the Lean stage.

lemma BG2_weights : ∀ i, ∑ j, (BG2.map (Rat.cast : ℚ → ℝ)) i j * ((![671,1000,296,296,1] : Fin 5 → ℝ) j)
    ≤ (2309/296 : ℝ) * (![671,1000,296,296,1] : Fin 5 → ℝ) i := by
  intro i; fin_cases i <;> simp [BG2, Fin.sum_univ_succ] <;> norm_num

/-! ### Endpoint -/

theorem specRad_G_gt : (781/400 : ℝ) < specRad (Aalpha (1/4) G) := by
  sorry -- DRAFT: root t of charpoly(BG) gives eigenvalue t/4 > 781/400 of A_{1/4}(G);
        -- the eigenvalue set is finite (nonempty, bounded), so sSup ≥ t/4.

theorem specRad_G2_lt : specRad (Aalpha (1/4) G2) < (781/400 : ℝ) := by
  sorry -- DRAFT: every eigenvalue μ of A_{1/4}(G'') is μ'/4 with μ' an eigenvalue of BG2;
        -- eig_le_of_weighted gives ‖μ'‖ ≤ 2309/296 < 781/100; sSup of a finite nonempty set.

/-- Literal negation of the fixed-strong-component reading of Conjecture 2.10
(arXiv v1) / Remark 3.8 (journal): with `G ∈ G_5^4` and `G2 = G''(G)`, at `α = 1/4`. -/
theorem conjecture_2_10_false :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧ specRad (Aalpha α G2) < specRad (Aalpha α G) :=
  ⟨1/4, by norm_num, by norm_num, lt_trans specRad_G2_lt specRad_G_gt⟩

end MathDB351804

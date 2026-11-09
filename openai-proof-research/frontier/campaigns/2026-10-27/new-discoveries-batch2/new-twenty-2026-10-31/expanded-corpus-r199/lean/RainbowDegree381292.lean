/-
  UNCOMPILED DRAFT (expanded-corpus-r199, Claude lane: Lean was NOT run here).
  MathDB 381292 / Aharoni–Howard arXiv:1605.06752, final conjecture of "Further conjectures".
  Literal model: F i ⊆ E(K_{n,n}) as Finset (Fin n × Fin n) of (left, right) pairs;
  a i j = deg_{F i}(v_j) for right vertex v_j; sorted rearrangement = insertionSort (· ≤ ·).
  We disprove the statement with the shifted family k = 4, n = 10:
     rows (1,0,..,0), (10,2,..,2), (10,3,..,3), (10,5,..,5); row sums 1, 28, 37, 55.
  Root/Sol: compile under the pinned toolchain; final endpoint must avoid native_decide.
-/
import Mathlib

namespace Rainbow381292

/-- degree of the right vertex j in F -/
def deg {n : ℕ} (F : Finset (Fin n × Fin n)) (j : Fin n) : ℕ :=
  (F.filter (fun e => e.2 = j)).card

/-- non-decreasing rearrangement -/
def srt (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

/-- sum of the j smallest entries -/
def psum (l : List ℕ) (j : ℕ) : ℕ := ((srt l).take j).sum

/-- MathDB 381292, literal: for all k ≤ n and all F_1..F_k ⊆ E(K_{n,n}), if
  Σ_{i≤j} r⃗_i > j(j-1)n for every 1 ≤ j ≤ k, then some π : [k] → [k] has
  Σ_{i≤j} (sorted a_{i,π(i)})_i > j(j-1) for every 1 ≤ j ≤ k. -/
def Statement : Prop :=
  ∀ (k n : ℕ) (hkn : k ≤ n) (F : Fin k → Finset (Fin n × Fin n)),
    (∀ j, 1 ≤ j → j ≤ k → j * (j - 1) * n < psum (List.ofFn fun i => (F i).card) j) →
    ∃ π : Equiv.Perm (Fin k), ∀ j, 1 ≤ j → j ≤ k →
      j * (j - 1) < psum (List.ofFn fun i => deg (F i) (Fin.castLE hkn (π i))) j

/-- the counterexample family at k = 4, n = 10 (all graphs bipartitely shifted) -/
def xval : Fin 4 → ℕ := ![0, 2, 3, 5]

def Fam : Fin 4 → Finset (Fin 10 × Fin 10) := fun i =>
  if i = 0 then {((0 : Fin 10), (0 : Fin 10))}
  else (Finset.univ.filter fun e : Fin 10 × Fin 10 => e.2 = 0 ∨ e.1.val < xval i)

theorem fam_hyp' : ∀ j ∈ Finset.Icc 1 4,
    j * (j - 1) * 10 < psum (List.ofFn fun i => (Fam i).card) j := by
  decide -- DRAFT: row sums 1, 28, 37, 55; prefix sums 1 > 0, 29 > 20, 66 > 60, 121 > 120

theorem fam_hyp : ∀ j, 1 ≤ j → j ≤ 4 →
    j * (j - 1) * 10 < psum (List.ofFn fun i => (Fam i).card) j :=
  fun j h1 h4 => fam_hyp' j (Finset.mem_Icc.mpr ⟨h1, h4⟩)

theorem fam_concl_fails' : ∀ π : Equiv.Perm (Fin 4), ∃ j ∈ Finset.Icc 1 4,
    ¬ (j * (j - 1) < psum (List.ofFn fun i => deg (Fam i) (Fin.castLE (by norm_num) (π i))) j) := by
  decide -- DRAFT: 24 permutations; π 0 ≠ 0 gives a 0 entry (j = 1 fails), else (1,2,3,5) fails at j = 4

theorem fam_concl_fails : ∀ π : Equiv.Perm (Fin 4), ∃ j, 1 ≤ j ∧ j ≤ 4 ∧
    ¬ (j * (j - 1) < psum (List.ofFn fun i => deg (Fam i) (Fin.castLE (by norm_num) (π i))) j) := by
  intro π
  obtain ⟨j, hj, hbad⟩ := fam_concl_fails' π
  exact ⟨j, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2, hbad⟩

theorem statement_false : ¬ Statement := by
  intro h
  obtain ⟨π, hπ⟩ := h 4 10 (by norm_num) Fam fam_hyp
  obtain ⟨j, hj1, hj4, hbad⟩ := fam_concl_fails π
  exact hbad (hπ j hj1 hj4)

end Rainbow381292

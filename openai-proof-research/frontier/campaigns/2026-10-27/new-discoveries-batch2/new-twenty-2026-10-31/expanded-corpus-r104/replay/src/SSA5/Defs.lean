import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order

/-!
# Secondary structure avoidance codes: source definitions

Literal transcription of the definitions in Chu, Wang and Zhang,
"Improved constructions of secondary structure avoidance codes for DNA sequences",
arXiv:2304.11403v1 (Section II, Definitions 1–5, Section III Definition 3, Section V, Conjecture 1).

* `Base` is the DNA alphabet `D = {A, T, C, G}` with Watson–Crick complement.
* `rc` is the reverse complement of a length-`m` word.
* `IsGeneratingSet m S`: `S ⊆ D^m` is a maximal set containing no two reverse-complement
  sequences `x, y` (not necessarily distinct) — the members of the family `S_m` of Definition 4.
* `TCDominant m`: the length-`m` words in which the number of `T` and `C` is larger than `m/2`.
* `code m n S`: the code `C_n(S)` of Definition 5, i.e. all `x ∈ D^n` such that every
  (consecutive) length-`m` subsequence `x[i; m]` belongs to `S`.
* `rateSeq m S n = (1/n) log₂ |C_n(S)|`, the code rate of `C_n(S)`; the rate of the generating
  set is its limit as `n → ∞` (Definition 2 / Theorem 6).
-/

namespace SSA

/-- The DNA alphabet. -/
inductive Base
  | A | C | G | T
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Base :=
  Fintype.ofList [.A, .C, .G, .T] (by intro x; cases x <;> simp)

/-- Watson–Crick complement: `T ↔ A`, `C ↔ G`. -/
def Base.comp : Base → Base
  | .A => .T
  | .T => .A
  | .C => .G
  | .G => .C

/-- Words (sequences) of length `m` over the DNA alphabet. -/
abbrev Word (m : ℕ) := Fin m → Base

/-- Reverse complement: `RC(x)_t = comp (x_{m-1-t})`. -/
def rc {m : ℕ} (x : Word m) : Word m := fun i => (x (Fin.rev i)).comp

/-- Definition 4: `S` is a maximal set of length-`m` sequences in which there are no two
reverse-complement sequences `x` and `y` (not necessarily distinct). -/
def IsGeneratingSet (m : ℕ) (S : Set (Word m)) : Prop :=
  (∀ x ∈ S, rc x ∉ S) ∧
    ∀ S' : Set (Word m), S ⊆ S' → (∀ x ∈ S', rc x ∉ S') → S' = S

/-- Number of occurrences of `T` and `C` in a word. -/
def tcCount {m : ℕ} (x : Word m) : ℕ :=
  (Finset.univ.filter (fun i => x i = Base.T ∨ x i = Base.C)).card

/-- The generating set of all TC-dominant length-`m` sequences: the number of `T` and `C`
is larger than `m / 2`. -/
def TCDominant (m : ℕ) : Set (Word m) := {x | (m : ℚ) / 2 < tcCount x}

/-- The consecutive subsequence `x[i; m] = (x_i, …, x_{i+m-1})` (0-based start `i`). -/
def window {n : ℕ} (m : ℕ) (x : Fin n → Base) (i : ℕ) (h : i + m ≤ n) : Word m :=
  fun j => x ⟨i + j, by omega⟩

open Classical in
/-- Definition 5: `C_n(S)`, all length-`n` sequences every length-`m` subsequence of which
belongs to `S`. -/
noncomputable def code (m n : ℕ) (S : Set (Word m)) : Finset (Fin n → Base) :=
  Finset.univ.filter (fun x => ∀ (i : ℕ) (h : i + m ≤ n), window m x i h ∈ S)

/-- The rate `(1/n) log₂ |C_n(S)|` (bits per nucleotide). -/
noncomputable def rateSeq (m : ℕ) (S : Set (Word m)) (n : ℕ) : ℝ :=
  Real.logb 2 ((code m n S).card : ℝ) / n

/-! ## Certificate data structure (not part of the statement) -/

/-- Complete 4-ary trees, used to store finite tables indexed by words. -/
inductive QT (α : Type)
  | leaf : α → QT α
  | node : QT α → QT α → QT α → QT α → QT α

/-- Look up a table entry; letters are ordered `A, C, G, T`. -/
def QT.get {α : Type} [Inhabited α] : QT α → List Base → α
  | .leaf a, _ => a
  | .node _ _ _ _, [] => default
  | .node a c g t, b :: l =>
    match b with
    | .A => a.get l
    | .C => c.get l
    | .G => g.get l
    | .T => t.get l

end SSA

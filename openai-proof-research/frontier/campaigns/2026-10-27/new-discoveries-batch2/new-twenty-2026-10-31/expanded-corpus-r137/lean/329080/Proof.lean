/-
UNCOMPILED DRAFT — lane expanded-corpus-r137 (Claude), 2026-11-03. Proof skeleton only: every lemma
below is stated with the exact role it plays in outputs/329080-proof.md; proofs are NOT written.
Root / Sol must fill, compile under -DwarningAsError=true, and audit #print axioms.
-/
import «Defs»
import «Base5Data»

namespace ChordGenus

variable {n : ℕ}

/-! ### Sub-diagrams -/

/-- Deleting the chord with letter `x` (relabel the remaining letters in order). -/
noncomputable def deleteChord (D : Diagram (n + 1)) (x : Fin (n + 1)) : Diagram n := sorry

/-- Restriction of a side assignment to the remaining endpoints. -/
noncomputable def restrictSides (D : Diagram (n + 1)) (x : Fin (n + 1)) (c : Sides (n + 1)) :
    Sides n := sorry

/-- Lemma 1 (deletion changes the boundary count by exactly one). Core permutation fact: inserting the
two darts of a chord replaces τℓ_p → a_p, τℓ_q → a_q by τℓ_p → p → a_q, τℓ_q → q → a_p, i.e. a
transposition of successors (cycle count ± 1), with the empty-circle corrections. -/
theorem boundary_delete (D : Diagram (n + 1)) (x : Fin (n + 1)) (c : Sides (n + 1)) :
    boundary (deleteChord D x) (restrictSides D x c) = boundary D c + 1 ∨
    boundary (deleteChord D x) (restrictSides D x c) + 1 = boundary D c := sorry

/-- Corollary 2 (heredity), stated for iterated deletion via a chord subset. -/
theorem maxGenus_mono_sub (D : Diagram n) (S : Finset (Fin n)) :
    True := trivial -- DRAFT placeholder: max/min genus of the sub-diagram on S ≤ that of D

/-! ### Lemma 3: bipartite interlacement gives a planar thickening -/

def crosses (D : Diagram n) (a b : Fin n) : Prop := sorry -- endpoints alternate

theorem genus_zero_of_bipartite (D : Diagram n) (side : Fin n → Bool)
    (h : ∀ a b, crosses D a b → side a ≠ side b) :
    ∃ c : Sides n, genus D c = 0 := sorry
  -- c i := side (D.word i); induction on n removing an innermost same-side chord (Lemma 1, +1 case)

/-! ### Lemma 4: five-chord base lemma (finite certificate) -/

/-- Predicate P on standard 5-chord words (see scripts/chord_cert.py). -/
def P5 (w : List Nat) : Bool := sorry -- DRAFT: transcribe `P` from scripts/chord_cert.py

/-- Computable dart face count on a list word with a bit mask (transcribe `dart_faces`). -/
def dartFaces (w : List Nat) (mask : Nat) : Nat := sorry

/-- All 945 standard words (first occurrences increasing) with 5 chords. -/
def standardWords5 : List (List Nat) := sorry

/-- Kernel-checkable: every standard word either satisfies P5 or has a listed witness with one face. -/
theorem base5_check :
    (standardWords5.all fun w => P5 w ||
      (Base5Data.witnesses.any fun e => e.1 == w && dartFaces w e.2 == 1)) = true := by
  sorry -- DRAFT: `decide` / `by rfl` after transcription; 945 words × ≤ 453 list lookups

/-- Bridge: `dartFaces` on the standard word of a diagram equals `boundary`. -/
theorem dartFaces_eq_boundary : True := trivial -- DRAFT placeholder

/-! ### Lemma 6: transfer lemma for (123123)(44⋯nn) -/

/-- State (d, s): d = b − m, s = inner/outer sides of the end edge on one boundary component. -/
theorem transfer_step : True := trivial -- DRAFT placeholder: rules of outputs/329080-proof.md Lemma 6

theorem genusRange_r3Block (n : ℕ) (hn : 3 ≤ n) : genusRange (r3Block n hn) = {1, 2} := sorry

/-! ### Main argument (Section 4 of the proof) -/

theorem unique_of_genusRange (n : ℕ) (hn : 5 ≤ n) (D : Diagram n) (h : genusRange D = {1, 2}) :
    Equivalent D (r3Block n (by omega)) := sorry
  -- 1. min genus 1 ⇒ interlacement not bipartite (genus_zero_of_bipartite)
  -- 2. shortest odd cycle is induced; length ≥ 5 ⇒ 5-chord sub-diagram with connected interlacement,
  --    contradicting base5_check (P5 part (a)) via heredity
  -- 3. triangle {a,b,c}; every pair x,y of other chords: sub-diagram {a,b,c,x,y} satisfies P5 part (b)
  -- 4. all extra chords in one arc, consecutive endpoints; rotate/rename to r3Block

end ChordGenus

/-
UNCOMPILED DRAFT — lane expanded-corpus-r137 (Claude), 2026-11-03.
No Lean, lake or leanchecker was run in this lane (Claude lane restriction). Root / a Sol worker must
compile, repair and audit. Target: Lean 4.34.1 + mathlib d13f23b7 (campaign pin).

Combinatorial model of thickened chord diagrams (MathDB 329080, Burns–Jonoska–Saito et al.,
arXiv:1410.6148, Definition 2.1 and Lemma 3.1), in the 2n-dart form validated in outputs/329080-proof.md §2.
-/
import Mathlib

namespace ChordGenus

/-- A chord diagram with `n` chords, read from a base point: a word of length `2n` over letters `Fin n`
in which every letter occurs exactly twice (source Section 2, "double-occurrence word"). -/
structure Diagram (n : ℕ) where
  word : Fin (2 * n) → Fin n
  twice : ∀ a : Fin n, (Finset.univ.filter (fun i => word i = a)).card = 2

variable {n : ℕ}

/-- The other endpoint of the chord through endpoint `i` (the involution τ). -/
noncomputable def partner (D : Diagram n) (i : Fin (2 * n)) : Fin (2 * n) :=
  -- the unique j ≠ i with word j = word i
  Classical.choose (show ∃ j, j ≠ i ∧ D.word j = D.word i from by
    sorry) -- DRAFT: obligation from `twice`; replace by a computable search in the final version

/-- A side assignment: `true` = band end attached to the OUTER boundary circle, `false` = inner. -/
abbrev Sides (n : ℕ) := Fin (2 * n) → Bool

/-- Next endpoint on the same boundary circle, following the induced boundary orientation:
increasing cyclic order on the inner circle, decreasing on the outer circle. If `i` is alone on its
circle the result is `i` itself (k = 2n). DRAFT: implement by `Nat.find` on `k ∈ [1, 2n]`. -/
noncomputable def nextSame (c : Sides n) (i : Fin (2 * n)) : Fin (2 * n) := sorry

/-- σ_c is a permutation (it cyclically orders each side). DRAFT obligation. -/
noncomputable def sigma (c : Sides n) : Equiv.Perm (Fin (2 * n)) := sorry

noncomputable def tau (D : Diagram n) : Equiv.Perm (Fin (2 * n)) := sorry

/-- Number of cycles (orbits, fixed points included) of a permutation of a finite type. -/
noncomputable def numCycles {α : Type*} [Fintype α] [DecidableEq α] (π : Equiv.Perm α) : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid π))

/-- Number of boundary components b(F) of the thickened diagram (dart model):
cycles of σ_c ∘ τ, plus one for each boundary circle carrying no band end. -/
noncomputable def boundary (D : Diagram n) (c : Sides n) : ℕ :=
  numCycles ((tau D).trans (sigma c)) +
    (if ∀ i, c i = true then 1 else 0) + (if ∀ i, c i = false then 1 else 0)

/-- Genus via the Euler characteristic (source Lemma 3.1): g = (n − b + 2)/2. -/
noncomputable def genus (D : Diagram n) (c : Sides n) : ℤ :=
  ((n : ℤ) - boundary D c + 2) / 2

/-- Genus range gr(D) (source Definition 2.1). -/
noncomputable def genusRange (D : Diagram n) : Set ℤ := Set.range (genus D)

/-- Equivalence of chord diagrams (source Section 2): cyclic rotation of the base point, reversal of
the reading direction, and renaming of letters. -/
def Equivalent (D E : Diagram n) : Prop :=
  ∃ (r : ℕ) (rev : Bool) (e : Equiv.Perm (Fin n)),
    ∀ i : Fin (2 * n),
      E.word i = e (D.word (if rev then
        ⟨(2 * n - 1 - ((i.val + r) % (2 * n))) % (2 * n), sorry⟩ -- DRAFT: bound
        else ⟨(i.val + r) % (2 * n), sorry⟩))

/-- The diagram (123123)(44 ⋯ nn) for n ≥ 3, letters 0-based: positions 0..5 read 0 1 2 0 1 2,
positions 6+2k and 7+2k both carry letter 3+k. -/
noncomputable def r3Block (n : ℕ) (hn : 3 ≤ n) : Diagram n := sorry -- DRAFT: explicit word + `twice`

end ChordGenus

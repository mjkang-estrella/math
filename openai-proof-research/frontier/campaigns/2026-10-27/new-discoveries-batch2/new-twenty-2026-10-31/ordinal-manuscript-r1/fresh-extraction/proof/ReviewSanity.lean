/-
  REVIEWER SUPPLEMENT (not part of the literal mathematical module `OrdinalLine`).
  Prints the literal definitions, re-states the two endpoints with their intended
  types, and adds small non-vacuity checks: the relations `Prec`/`Sim` are inhabited
  for concrete chains of the witness (including one that needs a non-identity
  permutation), the majorization conclusion is then the expected strict comparison,
  `EmbeddableInLine` is satisfiable for a two-point space, and the five comparisons of
  the non-embeddability certificate hold in the table.  Nothing here is used by the
  endpoints.
-/
import OrdinalLine
set_option warningAsError true
open OrdinalSpaces366371
#print IsOrdinalSpace
#print EmbeddableInLine
#print Prec
#print Sim
#print HasMajorization
#print MajorizationConjecture
#print D
#print δW
-- the endpoints have exactly the intended types
example : ¬ MajorizationConjecture := not_majorizationConjecture
example : IsOrdinalSpace δW ∧ Function.Bijective (id : Fin 6 → Fin 6) ∧
    HasMajorization δW (id : Fin 6 → Fin 6) ∧ ¬ EmbeddableInLine δW := witness
-- the conjecture's hypothesis on n is met: |Fin 6| = 6 > 0 and `id` enumerates Fin 6
example : Fintype.card (Fin 6) = 6 := Fintype.card_fin 6
-- the table (value D, rank 1..15) used in the paper
example : D 2 3 = 1 ∧ D 3 4 = 2 ∧ D 1 2 = 3 ∧ D 2 4 = 4 ∧ D 0 1 = 5 ∧ D 1 3 = 6 ∧
    D 1 4 = 7 ∧ D 4 5 = 8 ∧ D 3 5 = 9 ∧ D 0 2 = 10 ∧ D 2 5 = 11 ∧ D 0 3 = 12 ∧
    D 0 4 = 13 ∧ D 1 5 = 14 ∧ D 0 5 = 15 := by decide
-- the five comparisons of the certificate, and the forced-order comparisons
example : D 2 3 < D 3 4 ∧ D 1 2 < D 2 4 ∧ D 0 1 < D 1 3 ∧ D 1 4 < D 4 5 ∧ D 3 5 < D 0 2 := by
  decide
example : D 0 1 < D 0 2 ∧ D 0 2 < D 0 3 ∧ D 0 3 < D 0 4 ∧ D 0 4 < D 0 5 := by decide
-- non-vacuity of Prec (k = 1) and of the majorization conclusion
example : Prec δW (id : Fin 6 → Fin 6) (k := 1) ![2, 3] ![3, 4] :=
  ⟨1, by decide, by decide⟩
-- a strict majorization that needs the transposition: pieces (1, 9) against (10, 1)
example : Prec δW (id : Fin 6 → Fin 6) (k := 2) ![2, 3, 5] ![0, 2, 3] :=
  ⟨Equiv.swap 0 1, by decide, by decide⟩
example : δW 2 5 0 3 = .lt :=
  (majorization_W 2 (by decide) ![2, 3, 5] ![0, 2, 3] (by decide) (by decide)).1
    ⟨Equiv.swap 0 1, by decide, by decide⟩
-- non-vacuity of Sim: two different chains with repeats, pieces (0, 6, 2) and (6, 0, 2)
example : Sim δW (id : Fin 6 → Fin 6) (k := 3) ![1, 1, 3, 4] ![1, 3, 3, 4] :=
  ⟨Equiv.swap 0 1, by decide⟩
-- `EmbeddableInLine` is satisfiable: the two-point space with Φ = coercion to ℝ
example : EmbeddableInLine (fun x y z w : Fin 2 =>
    compare (if x = y then 0 else 1 : ℕ) (if z = w then 0 else 1)) := by
  refine ⟨fun i => ((i : ℕ) : ℝ), ?_⟩
  simp only [Fin.forall_fin_two]
  norm_num
  decide
#print axioms not_majorizationConjecture
#print axioms witness

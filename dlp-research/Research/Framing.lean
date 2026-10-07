import Research.Problem
import Research.SmallCurve

/-! Fixed-width input adequacy for the existing zero-padded tape semantics.

The width is an explicit, known parameter: reading that many cells recovers
the supplied list. Consequently distinct equal-width lists differ at an
observable head position. This does not claim secrecy, efficient decoding,
solver correctness, or a runtime bound, and introduces no acceptance policy.
The production lemmas do not depend on the deliberately leaky test encodings.
-/
namespace Research.Framing

theorem read_cons (left : List Bool) (b : Bool) (bs : List Bool) :
    ({ left := left, head := b, right := bs } : Machine.Tape).read (bs.length + 1) =
      b :: bs := by
  induction bs generalizing left b with
  | nil => rfl
  | cons c cs ih =>
    simp only [Machine.Tape.read, Machine.Tape.moveRight, List.length_cons] at ih ⊢
    exact congrArg (b :: ·) (ih _ _)

theorem read_ofBits (l : List Bool) : (Machine.Tape.ofBits l).read l.length = l := by
  cases l with
  | nil => rfl
  | cons b bs => exact read_cons [] b bs

theorem fixed_width_read (l : List Bool) (width : Nat) (h : l.length = width) :
    (Machine.Tape.ofBits l).read width = l := by
  rw [← h]
  exact read_ofBits l

theorem fixed_width_read_injective (a b : List Bool) (width : Nat)
    (ha : a.length = width) (hb : b.length = width)
    (h : (Machine.Tape.ofBits a).read width = (Machine.Tape.ofBits b).read width) :
    a = b := by
  rw [fixed_width_read a width ha, fixed_width_read b width hb] at h
  exact h

theorem fixed_width_reads_distinct (a b : List Bool) (width : Nat)
    (ha : a.length = width) (hb : b.length = width) (h : a ≠ b) :
    (Machine.Tape.ofBits a).read width ≠ (Machine.Tape.ofBits b).read width := by
  intro heq
  exact h (fixed_width_read_injective a b width ha hb heq)

/-- Tape position reached by exactly n applications of the existing moveRight.
This is an observation path, not a replacement interpreter. -/
def rightAt (t : Machine.Tape) : Nat → Machine.Tape
  | 0 => t
  | n + 1 => rightAt t.moveRight n

/-- Distinct finite reads contain a head observation distinguishing the tapes.
In particular, the result concerns accessible cells, not record inequality. -/
theorem read_difference_observable (t u : Machine.Tape) (width : Nat)
    (h : t.read width ≠ u.read width) :
    ∃ n, n < width ∧ (rightAt t n).head ≠ (rightAt u n).head := by
  induction width generalizing t u with
  | zero => exact False.elim (h rfl)
  | succ width ih =>
    by_cases hh : t.head = u.head
    · have htail : t.moveRight.read width ≠ u.moveRight.read width := by
        intro heq
        apply h
        simp only [Machine.Tape.read, hh, heq]
      obtain ⟨n, hn, hobs⟩ := ih t.moveRight u.moveRight htail
      exact ⟨n + 1, Nat.succ_lt_succ hn, hobs⟩
    · exact ⟨0, Nat.zero_lt_succ width, hh⟩

theorem fixed_width_observation_distinct (a b : List Bool) (width : Nat)
    (ha : a.length = width) (hb : b.length = width) (h : a ≠ b) :
    ∃ n, n < width ∧
      (rightAt (Machine.Tape.ofBits a) n).head ≠
        (rightAt (Machine.Tape.ofBits b) n).head :=
  read_difference_observable _ _ width (fixed_width_reads_distinct a b width ha hb h)

/-- The original interface already gives injectivity of the finite input
lists. This alone does not imply distinguishability under tape semantics. -/
theorem input_injective (P : CyclicProblem) (a b : Fin P.order)
    (h : P.input a = P.input b) : a = b := by
  apply P.distinct a b
  apply P.encode_injective
  exact List.append_cancel_left h

theorem input_length (P : CyclicProblem) (pointWidth : Nat)
    (hwidth : ∀ p, (P.encodePoint p).length = pointWidth) (d : Fin P.order) :
    (P.input d).length = P.parameters.length + pointWidth := by
  simp only [CyclicProblem.input, List.length_append, hwidth]

theorem input_read_roundtrip (P : CyclicProblem) (pointWidth : Nat)
    (hwidth : ∀ p, (P.encodePoint p).length = pointWidth) (d : Fin P.order) :
    (Machine.Tape.ofBits (P.input d)).read (P.parameters.length + pointWidth) =
      P.input d :=
  fixed_width_read _ _ (input_length P pointWidth hwidth d)

theorem input_read_injective (P : CyclicProblem) (pointWidth : Nat)
    (hwidth : ∀ p, (P.encodePoint p).length = pointWidth) (a b : Fin P.order)
    (h : (Machine.Tape.ofBits (P.input a)).read (P.parameters.length + pointWidth) =
      (Machine.Tape.ofBits (P.input b)).read (P.parameters.length + pointWidth)) :
    a = b := by
  apply input_injective P a b
  exact fixed_width_read_injective _ _ _
    (input_length P pointWidth hwidth a) (input_length P pointWidth hwidth b) h

theorem input_reads_distinct (P : CyclicProblem) (pointWidth : Nat)
    (hwidth : ∀ p, (P.encodePoint p).length = pointWidth) (a b : Fin P.order)
    (h : a ≠ b) :
    (Machine.Tape.ofBits (P.input a)).read (P.parameters.length + pointWidth) ≠
      (Machine.Tape.ofBits (P.input b)).read (P.parameters.length + pointWidth) := by
  intro heq
  exact h (input_read_injective P pointWidth hwidth a b heq)

theorem input_observation_distinct (P : CyclicProblem) (pointWidth : Nat)
    (hwidth : ∀ p, (P.encodePoint p).length = pointWidth) (a b : Fin P.order)
    (h : a ≠ b) :
    ∃ n, n < P.parameters.length + pointWidth ∧
      (rightAt (Machine.Tape.ofBits (P.input a)) n).head ≠
        (rightAt (Machine.Tape.ofBits (P.input b)) n).head :=
  read_difference_observable _ _ _ (input_reads_distinct P pointWidth hwidth a b h)

/-- SmallCurve has an eighteen-bit header and seven-bit coordinate encoding. -/
theorem smallCurve_input_length (d : Fin SmallCurve.problem.order) :
    (SmallCurve.problem.input d).length = 25 := by
  have hheader : SmallCurve.problem.parameters.length = 18 := by decide +kernel
  simpa only [hheader] using input_length SmallCurve.problem 7 SmallCurve.encode_width d

theorem smallCurve_input_read (d : Fin SmallCurve.problem.order) :
    (Machine.Tape.ofBits (SmallCurve.problem.input d)).read 25 =
      SmallCurve.problem.input d :=
  fixed_width_read _ _ (smallCurve_input_length d)

theorem smallCurve_input_reads_distinct (a b : Fin SmallCurve.problem.order) (h : a ≠ b) :
    (Machine.Tape.ofBits (SmallCurve.problem.input a)).read 25 ≠
      (Machine.Tape.ofBits (SmallCurve.problem.input b)).read 25 := by
  have hheader : SmallCurve.problem.parameters.length = 18 := by decide +kernel
  simpa only [hheader] using input_reads_distinct SmallCurve.problem 7 SmallCurve.encode_width a b h

theorem smallCurve_input_observation_distinct (a b : Fin SmallCurve.problem.order)
    (h : a ≠ b) :
    ∃ n, n < 25 ∧
      (rightAt (Machine.Tape.ofBits (SmallCurve.problem.input a)) n).head ≠
        (rightAt (Machine.Tape.ofBits (SmallCurve.problem.input b)) n).head :=
  read_difference_observable _ _ _ (smallCurve_input_reads_distinct a b h)

end Research.Framing

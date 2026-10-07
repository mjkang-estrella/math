import Research.OrbitArithmetic
import Research.BSGSArithmetic

/-! A high-level BSGS correctness baseline with explicit linear baby lookup.
The solver receives only public operations, a block width, and a target point.
Correctness is restricted to public keys on the reviewed cyclic orbit. Linear
lookup prevents a square-root total-work claim. No comparison, RAM, storage,
tape, or total coordinate-operation cost theorem is asserted in this module.
The inherited baby counter excludes generator evaluation and internal work.
-/
namespace Research.BSGS

open OrbitRefinement BSGSArithmetic

def lookup {Point : Type} [DecidableEq Point] : List (Point × Nat) → Point → Option Nat
  | [], _ => none
  | (p, j) :: rest, target => if p = target then some j else lookup rest target

theorem lookup_sound {Point : Type} [DecidableEq Point]
    (entries : List (Point × Nat)) (target : Point) (j : Nat)
    (h : lookup entries target = some j) : (target, j) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
    obtain ⟨p, k⟩ := entry
    by_cases hp : p = target
    · simp only [lookup, hp, ↓reduceIte] at h
      have hk : k = j := Option.some.inj h
      simp [hp, hk]
    · simp only [lookup, hp, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_complete {Point : Type} [DecidableEq Point]
    (entries : List (Point × Nat)) (target : Point) (j : Nat)
    (h : (target, j) ∈ entries) : ∃ k, lookup entries target = some k := by
  induction entries with
  | nil => simp at h
  | cons entry rest ih =>
    obtain ⟨p, k⟩ := entry
    by_cases hp : p = target
    · exact ⟨k, by simp [lookup, hp]⟩
    · have hr : (target, j) ∈ rest := by
        rcases List.mem_cons.mp h with heq | hr
        · have heqp : target = p := congrArg Prod.fst heq
          exact False.elim (hp heqp.symm)
        · exact hr
      obtain ⟨k', hk'⟩ := ih hr
      exact ⟨k', by simpa only [lookup, hp, ↓reduceIte] using hk'⟩

theorem baby_member (P : CyclicProblem) (A : OrbitArithmetic P) (m : Nat)
    (p : P.Point) (j : Nat) (h : (p, j) ∈ (buildBabies P A m).entries) :
    j < m ∧ p = orbit P j := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem h
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hi
  rw [buildBabies_length] at hlt
  have hpair : (p, j) = (orbit P i, i) :=
    Option.some.inj (hi.symm.trans (buildBabies_entry P A m i hlt))
  have hj : j = i := congrArg Prod.snd hpair
  have hp : p = orbit P i := congrArg Prod.fst hpair
  subst j
  exact ⟨hlt, hp⟩

/-- A bounded giant loop. Every failed lookup performs an actual addition by
the supplied stride before recursion. Modular output handles duplicate babies
when m exceeds the order. The loop may compute one unused final giant point. -/
def search (P : CyclicProblem) (A : OrbitArithmetic P) [DecidableEq P.Point]
    (entries : List (P.Point × Nat)) (stride : P.Point) (m i : Nat)
    (gamma : P.Point) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      match lookup entries gamma with
      | some j => some ((i * m + j) % P.order)
      | none => search P A entries stride m (i + 1) (A.add gamma stride) fuel

theorem giant_update (P : CyclicProblem) (A : OrbitArithmetic P) (m d i : Nat) :
    A.add (orbit P (d + i * negStride P.order m)) (orbit P (negStride P.order m)) =
      orbit P (d + (i + 1) * negStride P.order m) := by
  rw [A.add_orbit, Nat.add_mul, Nat.one_mul]
  congr 1
  omega

theorem search_correct (P : CyclicProblem) (A : OrbitArithmetic P) [DecidableEq P.Point]
    (m : Nat) (hm : 0 < m) (d : Fin P.order) (fuel i : Nat)
    (hlo : i ≤ d.val / m) (hhi : d.val / m < i + fuel) :
    search P A (buildBabies P A m).entries (orbit P (negStride P.order m)) m i
      (orbit P (d.val + i * negStride P.order m)) fuel = some d.val := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    cases hl : lookup (buildBabies P A m).entries
        (orbit P (d.val + i * negStride P.order m)) with
    | some j =>
      have hmem := lookup_sound _ _ _ hl
      obtain ⟨_, heq⟩ := baby_member P A m _ j hmem
      have hmatch := (orbit_eq_iff_mod P _ _).mp heq
      have hrec := recover P.order m d.val i j P.order_pos d.isLt hmatch
      simp only [search, hl, hrec]
    | none =>
      have hne : i ≠ d.val / m := by
        intro hi
        obtain ⟨_, hj, hmatch⟩ := complete_digits P.order m d.val P.order_pos hm d.isLt
        have heq : orbit P (d.val + i * negStride P.order m) = orbit P (d.val % m) := by
          apply (orbit_eq_iff_mod P _ _).mpr
          simpa only [hi] using hmatch
        have hmem : (orbit P (d.val + i * negStride P.order m), d.val % m) ∈
            (buildBabies P A m).entries := by
          rw [heq]
          exact List.mem_of_getElem? (buildBabies_entry P A m _ hj)
        obtain ⟨j, hj⟩ := lookup_complete _ _ _ hmem
        rw [hl] at hj
        contradiction
      simp only [search, hl]
      rw [giant_update]
      exact ih (i + 1) (by omega) (by omega)

/-- Uninstrumented executable solver. The table is constructed anew on every
invocation; no precomputed baby or inverse table is an input. -/
def solve (P : CyclicProblem) (A : OrbitArithmetic P) [DecidableEq P.Point]
    (m : Nat) (target : P.Point) : Option Nat :=
  let babies := buildBabies P A m
  let stride := A.neg babies.final
  search P A babies.entries stride m 0 target (blockCount P.order m)

theorem solve_correct (P : CyclicProblem) (A : OrbitArithmetic P) [DecidableEq P.Point]
    (m : Nat) (hm : 0 < m) (d : Fin P.order) : solve P A m (P.publicKey d) = some d.val := by
  dsimp only [solve]
  rw [buildBabies_final, A.neg_orbit]
  change search P A (buildBabies P A m).entries (orbit P (negStride P.order m)) m 0
    (orbit P d.val) (blockCount P.order m) = some d.val
  simpa only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] using
    search_correct P A m hm d (blockCount P.order m) 0 (Nat.zero_le _)
      (by simpa only [Nat.zero_add] using
        quotient_in_range P.order m d.val P.order_pos d.isLt)

def smallCurveSolve (m : Nat) (target : SmallCurve.Point) : Option Nat :=
  @solve SmallCurve.problem smallCurve (inferInstanceAs (DecidableEq SmallCurve.Point)) m target

theorem smallCurve_correct (m : Nat) (hm : 0 < m) (d : Fin SmallCurve.problem.order) :
    smallCurveSolve m (SmallCurve.problem.publicKey d) = some d.val :=
  @solve_correct SmallCurve.problem smallCurve (inferInstanceAs (DecidableEq SmallCurve.Point)) m hm d

/-- Every scalar, including zero, at unit, ordinary, exact-order and duplicate
baby widths. The generic theorem proves correctness for every positive width. -/
theorem smallCurve_edges : ∀ d : Fin 7,
    smallCurveSolve 1 (SmallCurve.multiple d.val) = some d.val ∧
    smallCurveSolve 3 (SmallCurve.multiple d.val) = some d.val ∧
    smallCurveSolve 7 (SmallCurve.multiple d.val) = some d.val ∧
    smallCurveSolve 8 (SmallCurve.multiple d.val) = some d.val := by
  decide +kernel

theorem order_one_correct (P : CyclicProblem) (A : OrbitArithmetic P) [DecidableEq P.Point]
    (hq : P.order = 1) (m : Nat) (hm : 0 < m) : solve P A m P.zero = some 0 := by
  have hd : 0 < P.order := by rw [hq]; decide
  exact solve_correct P A m hm ⟨0, hd⟩

end Research.BSGS

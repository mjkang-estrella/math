import Research.SortedBabies

/-! Conventional sorted BSGS with executed query counters. Preparation is
performed afresh but unpriced: baby generation, generator evaluation, key
construction, sorting, conversion, allocation and copying are excluded. Giant
arithmetic, scalar/control/bit work, physical array latency and memory are also
excluded. Thus the query bounds below are not total-work or tape bounds.
-/
namespace Research.SortedBSGS

open OrbitRefinement PointKeys BSGSArithmetic

structure Result where
  answer : Option Nat
  queries : Nat
  probes : Nat
  comparisonCalls : Nat
  deriving Repr, DecidableEq

def finish (answer : Option Nat) (query : IndexedLookup.Result) : Result :=
  ⟨answer, 1, query.probes, query.comparisonCalls⟩

def addQuery (rest : Result) (query : IndexedLookup.Result) : Result :=
  ⟨rest.answer, rest.queries + 1, rest.probes + query.probes,
    rest.comparisonCalls + query.comparisonCalls⟩

/-- The table is shared across giant queries within one invocation, and never
accepted as external inverse advice by solve. A final failed query may perform
one unused giant addition. Exhaustion is explicit in lookup and impossible by
its public-wrapper theorem; the defensive branch returns no answer. -/
def search (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (entries : Array IndexedLookup.Entry) (stride : P.Point) (m i : Nat)
    (gamma : P.Point) : Nat → Result
  | 0 => ⟨none, 0, 0, 0⟩
  | fuel + 1 =>
      let query := IndexedLookup.lookup entries (K.key gamma)
      match query.outcome with
      | .found j => finish (some ((i * m + j) % P.order)) query
      | .absent => addQuery (search P A K entries stride m (i + 1) (A.add gamma stride) fuel) query
      | .exhausted => finish none query

theorem search_correct (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (hm : 0 < m) (d : Fin P.order) (fuel i : Nat)
    (hlo : i ≤ d.val / m) (hhi : d.val / m < i + fuel) :
    (search P A K (SortedBabies.prepare P A K m).entries (orbit P (negStride P.order m)) m i
      (orbit P (d.val + i * negStride P.order m)) fuel).answer = some d.val := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    cases hl : (IndexedLookup.lookup (SortedBabies.prepare P A K m).entries
        (K.key (orbit P (d.val + i * negStride P.order m)))).outcome with
    | found j =>
      have hr := SortedBabies.lookup_recovers P A K m i d j hl
      simp only [search, hl, finish, hr]
    | exhausted =>
      exact False.elim (IndexedLookup.lookup_not_exhausted _ _ hl)
    | absent =>
      have hne : i ≠ d.val / m := by
        intro hi
        obtain ⟨_, hj, hmatch⟩ := complete_digits P.order m d.val P.order_pos hm d.isLt
        have heq : orbit P (d.val + i * negStride P.order m) = orbit P (d.val % m) := by
          apply (orbit_eq_iff_mod P _ _).mpr
          simpa only [hi] using hmatch
        obtain ⟨j, hfound⟩ := SortedBabies.lookup_baby P A K m (d.val % m) hj
        rw [heq] at hl
        rw [hl] at hfound
        contradiction
      simp only [search, hl, addQuery]
      rw [BSGS.giant_update]
      exact ih (i + 1) (by omega) (by omega)

def solve (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (target : P.Point) : Result :=
  let prepared := SortedBabies.prepare P A K m
  search P A K prepared.entries (A.neg prepared.final) m 0 target (blockCount P.order m)

theorem solve_correct (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (hm : 0 < m) (d : Fin P.order) :
    (solve P A K m (P.publicKey d)).answer = some d.val := by
  dsimp only [solve]
  rw [SortedBabies.prepare_final, A.neg_orbit]
  change (search P A K (SortedBabies.prepare P A K m).entries
    (orbit P (negStride P.order m)) m 0 (orbit P d.val) (blockCount P.order m)).answer = _
  simpa only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] using
    search_correct P A K m hm d (blockCount P.order m) 0 (Nat.zero_le _)
      (by simpa only [Nat.zero_add] using quotient_in_range P.order m d.val P.order_pos d.isLt)

theorem search_query_bounds (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (entries : Array IndexedLookup.Entry) (stride : P.Point) (m i : Nat)
    (gamma : P.Point) (fuel : Nat) :
    let result := search P A K entries stride m i gamma fuel
    result.queries ≤ fuel ∧
      result.probes ≤ fuel * IndexedLookup.fuelFor entries.size ∧
      result.comparisonCalls ≤ fuel * (2 * IndexedLookup.fuelFor entries.size) := by
  induction fuel generalizing i gamma with
  | zero => simp [search]
  | succ fuel ih =>
    have hp := IndexedLookup.lookup_probes_bound entries (K.key gamma)
    have hc := IndexedLookup.lookup_comparison_bound entries (K.key gamma)
    have hir := ih (i + 1) (A.add gamma stride)
    simp only [search]
    split
    · simp only [finish, Nat.succ_mul, Nat.zero_mul, Nat.zero_add] at *
      exact ⟨by omega, by omega, by omega⟩
    · simp only [addQuery, Nat.succ_mul, Nat.zero_mul, Nat.zero_add] at *
      exact ⟨by omega, by omega, by omega⟩
    · simp only [finish, Nat.succ_mul, Nat.zero_mul, Nat.zero_add] at *
      exact ⟨by omega, by omega, by omega⟩

theorem solve_query_bounds (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (target : P.Point) :
    (solve P A K m target).queries ≤ blockCount P.order m ∧
      (solve P A K m target).probes ≤ blockCount P.order m * IndexedLookup.fuelFor m ∧
      (solve P A K m target).comparisonCalls ≤
        blockCount P.order m * (2 * IndexedLookup.fuelFor m) := by
  simpa only [solve, SortedBabies.prepare_size] using
    search_query_bounds P A K (SortedBabies.prepare P A K m).entries
      (A.neg (SortedBabies.prepare P A K m).final) m 0 target (blockCount P.order m)

end Research.SortedBSGS

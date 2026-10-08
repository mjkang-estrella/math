import Std

/-! Counted binary lookup in an actual indexed array of cached natural keys.
The counters cover only explicit equality/ordering wrapper calls and probes.
They exclude key creation, table construction/sorting/conversion, allocation,
copying, scalar arithmetic, comparator bit work, reference counting, physical
array-access latency, and all tape/whole-solver costs. No RAM model is adopted.
Equal keys may carry different payloads; payloads are never array locations.
-/
namespace Research.IndexedLookup

structure Entry where
  key : Nat
  payload : Nat
  deriving Repr, DecidableEq

inductive Outcome where
  | found (payload : Nat)
  | absent
  | exhausted
  deriving Repr, DecidableEq

structure Result where
  outcome : Outcome
  probes : Nat
  equalityCalls : Nat
  orderingCalls : Nat
  deriving Repr, DecidableEq

structure Interval (size : Nat) where
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi
  bounded : hi ≤ size

def Interval.length {size : Nat} (r : Interval size) : Nat := r.hi - r.lo
def Interval.mid {size : Nat} (r : Interval size) : Nat := r.lo + r.length / 2

theorem mid_in_range {size : Nat} (r : Interval size) (h : r.lo < r.hi) :
    r.lo ≤ r.mid ∧ r.mid < r.hi := by
  have := r.ordered
  simp only [Interval.mid, Interval.length]
  omega

def Interval.left {size : Nat} (r : Interval size) (h : r.lo < r.hi) : Interval size :=
  ⟨r.lo, r.mid, (mid_in_range r h).1, Nat.le_trans (Nat.le_of_lt (mid_in_range r h).2) r.bounded⟩

def Interval.right {size : Nat} (r : Interval size) (h : r.lo < r.hi) : Interval size :=
  ⟨r.mid + 1, r.hi, (mid_in_range r h).2, r.bounded⟩

theorem left_half_length {size : Nat} (r : Interval size) (h : r.lo < r.hi) :
    (r.left h).length ≤ r.length / 2 := by
  simp only [Interval.left, Interval.length, Interval.mid]
  omega

theorem right_half_length {size : Nat} (r : Interval size) (h : r.lo < r.hi) :
    (r.right h).length ≤ r.length / 2 := by
  have := r.ordered
  simp only [Interval.right, Interval.length, Interval.mid]
  omega

def equalityTest (a b : Nat) : Bool × Nat := (a == b, 1)
def orderingTest (a b : Nat) : Bool × Nat := (decide (a < b), 1)

def emptyResult (outcome : Outcome) : Result := ⟨outcome, 0, 0, 0⟩
def foundResult (payload count : Nat) : Result := ⟨.found payload, 1, count, 0⟩
def bump (rest : Result) (eqCount orderCount : Nat) : Result :=
  ⟨rest.outcome, rest.probes + 1, rest.equalityCalls + eqCount,
    rest.orderingCalls + orderCount⟩

/-- Half-open indexed lookup. Empty intervals and exhausted fuel are distinct.
The midpoint and its entry are cached once per probe; no list view or slice is
used in executable lookup. Fuel bounds probes, not machine transitions. -/
def search (entries : Array Entry) (target : Nat) (r : Interval entries.size) : Nat → Result
  | 0 => emptyResult (if r.lo < r.hi then .exhausted else .absent)
  | fuel + 1 =>
      if h : r.lo < r.hi then
        let mid := r.mid
        have hm := mid_in_range r h
        let entry := entries[mid]'(Nat.lt_of_lt_of_le hm.2 r.bounded)
        let eqTest := equalityTest entry.key target
        if eqTest.1 then foundResult entry.payload eqTest.2
        else
          let ltTest := orderingTest entry.key target
          let rest := if ltTest.1 then
              search entries target
                ⟨mid + 1, r.hi, hm.2, r.bounded⟩ fuel
            else search entries target
              ⟨r.lo, mid, hm.1, Nat.le_trans (Nat.le_of_lt hm.2) r.bounded⟩ fuel
          bump rest eqTest.2 ltTest.2
      else emptyResult .absent

/-- Proof-oriented equation exposing the two recursive interval choices. -/
theorem search_step (entries : Array Entry) (target : Nat) (r : Interval entries.size)
    (fuel : Nat) (h : r.lo < r.hi) :
    search entries target r (fuel + 1) =
      if (entries[r.mid]'(Nat.lt_of_lt_of_le (mid_in_range r h).2 r.bounded)).key = target then
        foundResult (entries[r.mid]'(Nat.lt_of_lt_of_le (mid_in_range r h).2 r.bounded)).payload 1
      else if (entries[r.mid]'(Nat.lt_of_lt_of_le (mid_in_range r h).2 r.bounded)).key < target then
        bump (search entries target (r.right h) fuel) 1 1
      else bump (search entries target (r.left h) fuel) 1 1 := by
  simp [search, h, equalityTest, orderingTest, Interval.right, Interval.left]
  split
  · rfl
  · split <;> rfl

theorem search_empty (entries : Array Entry) (target : Nat) (r : Interval entries.size)
    (fuel : Nat) (h : r.lo = r.hi) : search entries target r fuel = emptyResult .absent := by
  cases fuel <;> simp [search, h]

theorem equalityCalls_eq_probes (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel : Nat) :
    (search entries target r fuel).equalityCalls = (search entries target r fuel).probes := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : r.lo < r.hi
    · rw [search_step entries target r fuel h]
      split
      · rfl
      · split <;> simp only [bump, ih]
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r _ he]
      rfl

theorem orderingCalls_le_probes (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel : Nat) :
    (search entries target r fuel).orderingCalls ≤ (search entries target r fuel).probes := by
  induction fuel generalizing r with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    by_cases h : r.lo < r.hi
    · rw [search_step entries target r fuel h]
      split
      · exact Nat.zero_le _
      · split <;> exact Nat.add_le_add_right (ih _) 1
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r _ he]
      exact Nat.le_refl _

def Outcome.foundFlag : Outcome → Nat
  | .found _ => 1
  | _ => 0

theorem count_shape (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel : Nat) :
    (search entries target r fuel).orderingCalls +
      (search entries target r fuel).outcome.foundFlag =
        (search entries target r fuel).probes := by
  induction fuel generalizing r with
  | zero => simp only [search, emptyResult]; split <;> rfl
  | succ fuel ih =>
    by_cases h : r.lo < r.hi
    · rw [search_step entries target r fuel h]
      split
      · rfl
      · split
        · simp only [bump]
          have hc := ih (r.right h)
          omega
        · simp only [bump]
          have hc := ih (r.left h)
          omega
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r _ he]
      rfl

theorem found_counts (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel payload : Nat)
    (h : (search entries target r fuel).outcome = .found payload) :
    0 < (search entries target r fuel).probes ∧
      (search entries target r fuel).orderingCalls =
        (search entries target r fuel).probes - 1 := by
  have hc := count_shape entries target r fuel
  rw [h] at hc
  simp only [Outcome.foundFlag] at hc
  omega

theorem absent_counts (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel : Nat)
    (h : (search entries target r fuel).outcome = .absent) :
    (search entries target r fuel).orderingCalls = (search entries target r fuel).probes := by
  have hc := count_shape entries target r fuel
  rw [h] at hc
  exact hc

private theorem half_lt_power (n k : Nat) (h : n < 2 ^ (k + 1)) : n / 2 < 2 ^ k := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
  simpa only [Nat.pow_succ] using h

theorem probes_power_bound (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel k : Nat) (h : r.length < 2 ^ k) :
    (search entries target r fuel).probes ≤ k := by
  induction k generalizing r fuel with
  | zero =>
    have he : r.lo = r.hi := by
      have := r.ordered
      simp only [Interval.length, Nat.pow_zero] at h
      omega
    rw [search_empty entries target r fuel he]
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hp : r.lo < r.hi
    · have hh : r.length / 2 < 2 ^ k := half_lt_power _ _ h
      cases fuel with
      | zero => exact Nat.zero_le _
      | succ fuel =>
        rw [search_step entries target r fuel hp]
        split
        · exact Nat.succ_le_succ (Nat.zero_le k)
        · split
          · exact Nat.add_le_add_right
              (ih (r.right hp) fuel (Nat.lt_of_le_of_lt (right_half_length r hp) hh)) 1
          · exact Nat.add_le_add_right
              (ih (r.left hp) fuel (Nat.lt_of_le_of_lt (left_half_length r hp) hh)) 1
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r fuel he]
      exact Nat.zero_le _

theorem adequate_not_exhausted (entries : Array Entry) (target : Nat)
    (r : Interval entries.size) (fuel : Nat) (h : r.length < 2 ^ fuel) :
    (search entries target r fuel).outcome ≠ .exhausted := by
  induction fuel generalizing r with
  | zero =>
    have he : r.lo = r.hi := by
      have := r.ordered
      simp only [Interval.length, Nat.pow_zero] at h
      omega
    rw [search_empty entries target r _ he]
    decide
  | succ fuel ih =>
    by_cases hp : r.lo < r.hi
    · have hh : r.length / 2 < 2 ^ fuel := half_lt_power _ _ h
      rw [search_step entries target r fuel hp]
      split
      · simp [foundResult]
      · split
        · exact ih (r.right hp) (Nat.lt_of_le_of_lt (right_half_length r hp) hh)
        · exact ih (r.left hp) (Nat.lt_of_le_of_lt (left_half_length r hp) hh)
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r _ he]
      decide

/-- Nondecreasing keys only: entries with equal keys may have any payloads. -/
def Nondecreasing (entries : Array Entry) : Prop :=
  ∀ i j (hi : i < entries.size) (hj : j < entries.size), i ≤ j →
    (entries[i]'hi).key ≤ (entries[j]'hj).key

def HasMatch (entries : Array Entry) (target : Nat) (r : Interval entries.size) : Prop :=
  ∃ (location : Nat) (hbound : location < entries.size),
    r.lo ≤ location ∧ location < r.hi ∧ (entries[location]'hbound).key = target

/-- Soundness needs neither sortedness nor adequate fuel. The witness is an
array location within the interval; it need not equal the returned payload. -/
theorem search_sound (entries : Array Entry) (target : Nat) (r : Interval entries.size)
    (fuel payload : Nat) (hfound : (search entries target r fuel).outcome = .found payload) :
    ∃ (location : Nat) (hbound : location < entries.size),
      r.lo ≤ location ∧ location < r.hi ∧
        (entries[location]'hbound).key = target ∧ (entries[location]'hbound).payload = payload := by
  induction fuel generalizing r with
  | zero => simp only [search, emptyResult] at hfound; split at hfound <;> contradiction
  | succ fuel ih =>
    by_cases hp : r.lo < r.hi
    · rw [search_step entries target r fuel hp] at hfound
      split at hfound
      · rename_i heq
        have hpayload := Outcome.found.inj hfound
        have hm := mid_in_range r hp
        exact ⟨r.mid, Nat.lt_of_lt_of_le hm.2 r.bounded, hm.1, hm.2, heq, hpayload⟩
      · split at hfound
        · obtain ⟨loc, hb, hlo, hhi, hk, hj⟩ := ih (r.right hp) hfound
          refine ⟨loc, hb, ?_, hhi, hk, hj⟩
          have hm := (mid_in_range r hp).1
          change r.mid + 1 ≤ loc at hlo
          omega
        · obtain ⟨loc, hb, hlo, hhi, hk, hj⟩ := ih (r.left hp) hfound
          refine ⟨loc, hb, hlo, ?_, hk, hj⟩
          have hm := (mid_in_range r hp).2
          change loc < r.mid at hhi
          omega
    · have he : r.lo = r.hi := by have := r.ordered; omega
      rw [search_empty entries target r _ he] at hfound
      contradiction

theorem search_complete (entries : Array Entry) (target : Nat)
    (hsorted : Nondecreasing entries) (r : Interval entries.size) (fuel : Nat)
    (hadequate : r.length < 2 ^ fuel) (hmatch : HasMatch entries target r) :
    ∃ payload, (search entries target r fuel).outcome = .found payload := by
  induction fuel generalizing r with
  | zero =>
    obtain ⟨loc, hb, hlo, hhi, hk⟩ := hmatch
    simp only [Interval.length, Nat.pow_zero] at hadequate
    have := r.ordered
    omega
  | succ fuel ih =>
    obtain ⟨loc, hb, hlo, hhi, hk⟩ := hmatch
    have hp : r.lo < r.hi := by omega
    have hm := mid_in_range r hp
    have hmb : r.mid < entries.size := Nat.lt_of_lt_of_le hm.2 r.bounded
    have hh : r.length / 2 < 2 ^ fuel := half_lt_power _ _ hadequate
    rw [search_step entries target r fuel hp]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      split
      · rename_i hlt
        have hloc : r.mid + 1 ≤ loc := by
          by_cases hle : loc ≤ r.mid
          · have hs := hsorted loc r.mid hb hmb hle
            rw [hk] at hs
            omega
          · omega
        have hchild : HasMatch entries target (r.right hp) := ⟨loc, hb, hloc, hhi, hk⟩
        exact ih (r.right hp) (Nat.lt_of_le_of_lt (right_half_length r hp) hh) hchild
      · rename_i hnlt
        have hloc : loc < r.mid := by
          by_cases hle : r.mid ≤ loc
          · have hs := hsorted r.mid loc hmb hb hle
            rw [hk] at hs
            omega
          · omega
        have hchild : HasMatch entries target (r.left hp) := ⟨loc, hb, hlo, hloc, hk⟩
        exact ih (r.left hp) (Nat.lt_of_le_of_lt (left_half_length r hp) hh) hchild

theorem search_absent_iff (entries : Array Entry) (target : Nat)
    (hsorted : Nondecreasing entries) (r : Interval entries.size) (fuel : Nat)
    (hadequate : r.length < 2 ^ fuel) :
    (search entries target r fuel).outcome = .absent ↔ ¬ HasMatch entries target r := by
  constructor
  · intro habsent hmatch
    obtain ⟨payload, hp⟩ := search_complete entries target hsorted r fuel hadequate hmatch
    rw [habsent] at hp
    contradiction
  · intro hnone
    have hne := adequate_not_exhausted entries target r fuel hadequate
    cases ho : (search entries target r fuel).outcome with
    | absent => rfl
    | exhausted => exact False.elim (hne ho)
    | found payload =>
      obtain ⟨loc, hb, hlo, hhi, hk, hj⟩ := search_sound entries target r fuel payload ho
      exact False.elim (hnone ⟨loc, hb, hlo, hhi, hk⟩)

def fullInterval (entries : Array Entry) : Interval entries.size :=
  ⟨0, entries.size, Nat.zero_le _, Nat.le_refl _⟩

def fuelFor (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

theorem fuelFor_adequate (n : Nat) : n < 2 ^ fuelFor n := by
  by_cases hn : n = 0
  · simp [fuelFor, hn]
  · simp only [fuelFor, hn, ↓reduceIte]
    exact (Nat.log2_lt hn).mp (Nat.lt_succ_self _)

def lookup (entries : Array Entry) (target : Nat) : Result :=
  search entries target (fullInterval entries) (fuelFor entries.size)

theorem lookup_not_exhausted (entries : Array Entry) (target : Nat) :
    (lookup entries target).outcome ≠ .exhausted := by
  apply adequate_not_exhausted
  simpa only [fullInterval, Interval.length, Nat.sub_zero] using fuelFor_adequate entries.size

theorem lookup_probes_bound (entries : Array Entry) (target : Nat) :
    (lookup entries target).probes ≤ fuelFor entries.size := by
  apply probes_power_bound
  simpa only [fullInterval, Interval.length, Nat.sub_zero] using fuelFor_adequate entries.size

theorem lookup_log_bound (entries : Array Entry) (target : Nat) (h : entries.size ≠ 0) :
    (lookup entries target).probes ≤ Nat.log2 entries.size + 1 := by
  simpa only [fuelFor, h, ↓reduceIte] using lookup_probes_bound entries target

theorem lookup_sound (entries : Array Entry) (target payload : Nat)
    (h : (lookup entries target).outcome = .found payload) :
    ∃ (location : Nat) (hbound : location < entries.size),
      (entries[location]'hbound).key = target ∧ (entries[location]'hbound).payload = payload := by
  obtain ⟨loc, hb, hlo, hhi, hk, hj⟩ := search_sound entries target _ _ payload h
  exact ⟨loc, hb, hk, hj⟩

theorem lookup_complete (entries : Array Entry) (target : Nat) (hsorted : Nondecreasing entries)
    (h : ∃ (location : Nat) (hbound : location < entries.size), (entries[location]'hbound).key = target) :
    ∃ payload, (lookup entries target).outcome = .found payload := by
  apply search_complete entries target hsorted
  · simpa only [fullInterval, Interval.length, Nat.sub_zero] using fuelFor_adequate entries.size
  · obtain ⟨loc, hb, hk⟩ := h
    exact ⟨loc, hb, Nat.zero_le _, hb, hk⟩

theorem lookup_absent_iff (entries : Array Entry) (target : Nat) (hsorted : Nondecreasing entries) :
    (lookup entries target).outcome = .absent ↔
      ¬ ∃ (location : Nat) (hbound : location < entries.size), (entries[location]'hbound).key = target := by
  rw [lookup, search_absent_iff entries target hsorted]
  · constructor
    · intro hnone hsome
      obtain ⟨loc, hb, hk⟩ := hsome
      exact hnone ⟨loc, hb, Nat.zero_le _, hb, hk⟩
    · intro hnone hsome
      obtain ⟨loc, hb, hlo, hhi, hk⟩ := hsome
      exact hnone ⟨loc, hb, hk⟩
  · simpa only [fullInterval, Interval.length, Nat.sub_zero] using fuelFor_adequate entries.size

theorem lookup_empty (entries : Array Entry) (target : Nat) (h : entries.size = 0) :
    lookup entries target = emptyResult .absent := by
  apply search_empty
  exact h.symm

theorem lookup_count_relations (entries : Array Entry) (target : Nat) :
    (lookup entries target).equalityCalls = (lookup entries target).probes ∧
      (lookup entries target).orderingCalls ≤ (lookup entries target).probes :=
  ⟨equalityCalls_eq_probes entries target _ _, orderingCalls_le_probes entries target _ _⟩

theorem lookup_found_counts (entries : Array Entry) (target payload : Nat)
    (h : (lookup entries target).outcome = .found payload) :
    0 < (lookup entries target).probes ∧
      (lookup entries target).orderingCalls = (lookup entries target).probes - 1 :=
  found_counts entries target _ _ payload h

theorem lookup_absent_counts (entries : Array Entry) (target : Nat)
    (h : (lookup entries target).outcome = .absent) :
    (lookup entries target).orderingCalls = (lookup entries target).probes :=
  absent_counts entries target _ _ h

theorem lookup_probes_power_bound (entries : Array Entry) (target k : Nat)
    (h : entries.size < 2 ^ k) : (lookup entries target).probes ≤ k := by
  apply probes_power_bound
  simpa only [fullInterval, Interval.length, Nat.sub_zero] using h

/-- Sum of the two explicit comparison-call counters, not a runtime measure. -/
def Result.comparisonCalls (r : Result) : Nat := r.equalityCalls + r.orderingCalls

theorem lookup_comparison_bound (entries : Array Entry) (target : Nat) :
    (lookup entries target).comparisonCalls ≤ 2 * fuelFor entries.size := by
  obtain ⟨heq, hle⟩ := lookup_count_relations entries target
  have hp := lookup_probes_bound entries target
  unfold Result.comparisonCalls
  omega

theorem lookup_comparison_log_bound (entries : Array Entry) (target : Nat)
    (h : entries.size ≠ 0) :
    (lookup entries target).comparisonCalls ≤ 2 * (Nat.log2 entries.size + 1) := by
  simpa only [fuelFor, h, ↓reduceIte] using lookup_comparison_bound entries target

private def boundaryTable : Array Entry := #[⟨2, 99⟩, ⟨4, 42⟩, ⟨8, 777⟩]
private def duplicateTable : Array Entry := #[⟨1, 10⟩, ⟨2, 11⟩, ⟨2, 99⟩, ⟨4, 44⟩]
private def sameTable : Array Entry := #[⟨5, 10⟩, ⟨5, 20⟩, ⟨5, 30⟩, ⟨5, 40⟩]
private def powerFour : Array Entry := #[⟨0, 10⟩, ⟨2, 11⟩, ⟨4, 12⟩, ⟨6, 13⟩]
private def powerEight : Array Entry :=
  #[⟨0, 80⟩, ⟨2, 81⟩, ⟨4, 82⟩, ⟨6, 83⟩, ⟨8, 84⟩, ⟨10, 85⟩, ⟨12, 86⟩, ⟨14, 87⟩]

/-- Finite execution checks: empty/unit, absence below/above/between keys,
duplicate keys with different payloads, all-equal keys, and power-of-two sizes.
Payload 99 is returned from location 2 in the duplicate example. -/
theorem boundary_checks :
    lookup #[] 2 = ⟨.absent, 0, 0, 0⟩ ∧
    lookup #[⟨2, 99⟩] 2 = ⟨.found 99, 1, 1, 0⟩ ∧
    (lookup boundaryTable 0).outcome = .absent ∧
    (lookup boundaryTable 9).outcome = .absent ∧
    (lookup boundaryTable 6).outcome = .absent ∧
    (lookup boundaryTable 8).outcome = .found 777 ∧
    lookup duplicateTable 2 = ⟨.found 99, 1, 1, 0⟩ ∧
    lookup sameTable 5 = ⟨.found 30, 1, 1, 0⟩ ∧
    (lookup sameTable 4).outcome = .absent ∧
    (lookup sameTable 6).outcome = .absent ∧
    lookup powerFour 0 = ⟨.found 10, 3, 3, 2⟩ ∧
    lookup powerFour 1 = ⟨.absent, 3, 3, 3⟩ ∧
    lookup powerEight 0 = ⟨.found 80, 4, 4, 3⟩ ∧
    lookup powerEight 1 = ⟨.absent, 4, 4, 4⟩ := by
  decide +kernel

theorem exhaustion_is_distinct :
    search boundaryTable 6 (fullInterval boundaryTable) 0 = ⟨.exhausted, 0, 0, 0⟩ ∧
      (lookup boundaryTable 6).outcome = .absent := by
  decide +kernel

end Research.IndexedLookup

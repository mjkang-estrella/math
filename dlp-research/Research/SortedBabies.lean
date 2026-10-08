import Research.BSGS
import Research.PointKey
import Research.IndexedLookup

/-! Correctness-only preparation for sorted BSGS. Every invocation constructs
babies, computes cached keys, converts to an array and sorts it. None of this
preprocessing is priced here. In particular, library merge sort carries no
claimed two-buffer space bound, and generator evaluation remains unpriced.
Public encodings, the tape machine and its goals are unchanged.
-/
namespace Research.SortedBabies

open OrbitRefinement PointKeys IndexedLookup

structure Prepared (P : CyclicProblem) where
  entries : Array Entry
  final : P.Point

def keyEntry (P : CyclicProblem) (K : PointKey P) (pair : P.Point × Nat) : Entry :=
  ⟨K.key pair.1, pair.2⟩

def keyLE (a b : Entry) : Bool := decide (a.key ≤ b.key)

/-- Cache coordinate keys once per generated baby, and order only by keys.
Duplicate keys retain their payloads; scalar payload is never a tie-breaker. -/
def prepare (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P) (m : Nat) :
    Prepared P :=
  let babies := buildBabies P A m
  ⟨(babies.entries.map (keyEntry P K)).toArray.mergeSort keyLE, babies.final⟩

theorem prepare_size (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) : (prepare P A K m).entries.size = m := by
  simp [prepare, buildBabies_length]

theorem prepare_final (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) : (prepare P A K m).final = orbit P m :=
  buildBabies_final P A m

theorem prepare_mem (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (entry : Entry) :
    entry ∈ (prepare P A K m).entries ↔
      ∃ pair ∈ (buildBabies P A m).entries, keyEntry P K pair = entry := by
  simp [prepare, List.mem_map]

theorem prepare_sound (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) (entry : Entry) (h : entry ∈ (prepare P A K m).entries) :
    entry.payload < m ∧ entry.key = K.key (orbit P entry.payload) := by
  obtain ⟨⟨point, j⟩, hm, he⟩ := (prepare_mem P A K m entry).mp h
  obtain ⟨hj, hp⟩ := BSGS.baby_member P A m point j hm
  subst entry
  simpa [keyEntry, hp] using And.intro hj (Eq.refl (K.key (orbit P j)))

theorem prepare_complete (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m j : Nat) (hj : j < m) :
    (⟨K.key (orbit P j), j⟩ : Entry) ∈ (prepare P A K m).entries := by
  apply (prepare_mem P A K m _).mpr
  exact ⟨(orbit P j, j), List.mem_of_getElem? (buildBabies_entry P A m j hj), rfl⟩

theorem prepare_pairwise (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) :
    (prepare P A K m).entries.toList.Pairwise (fun a b => a.key ≤ b.key) := by
  have hs := @Array.pairwise_mergeSort Entry keyLE
    (by intro a b c hab hbc; simp only [keyLE, decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [keyLE, Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((buildBabies P A m).entries.map (keyEntry P K)).toArray
  simpa only [prepare, keyLE, decide_eq_true_eq] using hs

theorem prepare_ordered (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m i j : Nat) (hi : i < (prepare P A K m).entries.size)
    (hj : j < (prepare P A K m).entries.size) (hij : i ≤ j) :
    ((prepare P A K m).entries[i]'hi).key ≤
      ((prepare P A K m).entries[j]'hj).key := by
  by_cases heq : i = j
  · subst j
    exact Nat.le_refl _
  · have hs := List.pairwise_iff_getElem.mp (prepare_pairwise P A K m)
    exact hs i j hi hj (by omega)

theorem prepare_nondecreasing (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m : Nat) : Nondecreasing (prepare P A K m).entries :=
  prepare_ordered P A K m

theorem lookup_baby (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m j : Nat) (hj : j < m) :
    ∃ payload, (IndexedLookup.lookup (prepare P A K m).entries (K.key (orbit P j))).outcome =
      .found payload := by
  apply IndexedLookup.lookup_complete _ _ (prepare_nondecreasing P A K m)
  obtain ⟨loc, hb, he⟩ := Array.mem_iff_getElem.mp (prepare_complete P A K m j hj)
  exact ⟨loc, hb, congrArg Entry.key he⟩

/-- A matching cached key on a giant orbit recovers d using the stored scalar
payload, regardless of the entry's sorted location or duplicate baby keys. -/
theorem match_recovers (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m i : Nat) (d : Fin P.order) (entry : Entry)
    (hmem : entry ∈ (prepare P A K m).entries)
    (hkey : entry.key = K.key (orbit P (d.val + i * BSGSArithmetic.negStride P.order m))) :
    (i * m + entry.payload) % P.order = d.val := by
  obtain ⟨_, he⟩ := prepare_sound P A K m entry hmem
  have hp := (K.reflects_orbit _ _).mp (he.symm.trans hkey)
  have hr := (orbit_eq_iff_mod P _ _).mp hp.symm
  exact BSGSArithmetic.recover P.order m d.val i entry.payload P.order_pos d.isLt hr

theorem lookup_recovers (P : CyclicProblem) (A : OrbitArithmetic P) (K : PointKey P)
    (m i : Nat) (d : Fin P.order) (payload : Nat)
    (h : (IndexedLookup.lookup (prepare P A K m).entries
      (K.key (orbit P (d.val + i * BSGSArithmetic.negStride P.order m)))).outcome =
        .found payload) :
    (i * m + payload) % P.order = d.val := by
  obtain ⟨loc, hb, hk, hp⟩ := IndexedLookup.lookup_sound _ _ payload h
  have hr := match_recovers P A K m i d _ (Array.getElem_mem hb) hk
  simpa only [hp] using hr

/-- Specializations include empty, unit, ordinary, exact-order and duplicated
baby tables. This is derived from the generic proofs, not native evaluation. -/
theorem smallCurve_edges : ∀ m : Fin 9,
    (prepare SmallCurve.problem OrbitRefinement.smallCurve PointKeys.smallCurve m.val).entries.size =
        m.val ∧
    ∀ j : Fin m.val,
      (⟨PointKeys.coordinateKey (SmallCurve.multiple j.val), j.val⟩ : Entry) ∈
        (prepare SmallCurve.problem OrbitRefinement.smallCurve PointKeys.smallCurve m.val).entries := by
  intro m
  refine ⟨prepare_size _ _ _ _, ?_⟩
  intro j
  exact prepare_complete _ _ _ m.val j.val j.isLt

end Research.SortedBabies

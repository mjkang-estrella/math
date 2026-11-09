import SemCanonical
import SemPeriodic
namespace ChanLevine

/-- Unproved cycle-specific removal/least-action direction, not an axiom. -/
def ClosedWordRecurrence : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (c : SignedConfig n) (w : List (ZMod n)),
    w ≠ [] → LegalWord c w c → Recurrent c

/-- Unproved construction of a return word from the facing-pair test. -/
def CycleTestWord : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : Config n,
    CycleTest c → ∃ w, w ≠ [] ∧ LegalWord c.lift w c.lift

/-- Unproved obstruction argument for empty rotor cycles. -/
def ClosedWordCycleTest : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (c : Config n) (w : List (ZMod n)),
    w ≠ [] → LegalWord c.lift w c.lift → CycleTest c

/-- Unproved sink-normalization/classification lemma; the uniqueness bottleneck. -/
def RecurrentNormalization : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : Config n, NatRecurrent c →
    Reach c.lift (canonical (chipLevel c) (chipWeight c)).lift

/-- CONDITIONAL on exactly the three stated closed-word obligations. -/
theorem cycleTestBridge (hr : ClosedWordRecurrence) (hw : CycleTestWord)
    (ht : ClosedWordCycleTest) : CycleTestBridge := by
  intro n inst hn c
  constructor
  · intro hc
    obtain ⟨w, hne, hl⟩ := recurrent_closed_word hc
    exact ht n hn c w hne hl
  · intro hc
    obtain ⟨w, hne, hl⟩ := hw n hn c hc
    exact hr n hn c.lift w hne hl

/-- Unconditional semantic target. -/
theorem canonicalTest : CanonicalTest := by
  intro n m inst hn hm i
  exact ⟨canonical_cycleTest hn hm i, canonical_weight m i⟩

/-- CONDITIONAL on the explicit recurrent normalization lemma. -/
theorem connectedFibres (hnorm : RecurrentNormalization) : ConnectedFibres := by
  intro n inst hn a b ha hb hl hw
  refine ⟨(canonical (chipLevel a) (chipWeight a)).lift, hnorm n hn a ha, ?_⟩
  rw [hl, hw]
  exact hnorm n hn b hb

/-- CONDITIONAL on graph-specific closed-trajectory coverage. -/
theorem ambientBridge (hcover : ClosedCoverage) : AmbientBridge :=
  ambientBridge_of_coverage hcover
end ChanLevine

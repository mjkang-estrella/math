import Dynamics
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators
namespace ChanLevine
variable {n : ℕ} [NeZero n]

def chipLevel (c : Config n) : ℕ := ∑ k, c.x k
def chipWeight (c : Config n) : ZMod n := weight c.lift

theorem level_lift (c : Config n) : level c.lift = (chipLevel c : ℤ) := by
  simp [level, Config.lift, chipLevel]

/-- The proposed specialised cycle test. This is NOT the recurrence definition. -/
def CycleTest (c : Config n) : Prop :=
  (∀ k, c.q k = true → c.q (k+1) = false → c.x k ≠ 0 ∨ c.x (k+1) ≠ 0) ∧
  ((∀ k, c.q k = true) → ∃ k, c.x k ≠ 0) ∧
  ((∀ k, c.q k = false) → ∃ k, c.x k ≠ 0)

def canonical (m : ℕ) (i : ZMod n) : Config n :=
  ⟨fun k => if k = 0 then m else 0,
    fun k => if 1 ≤ k.val ∧ k.val ≤ i.val then false else true⟩

theorem canonical_level (m : ℕ) (i : ZMod n) : chipLevel (canonical m i) = m := by
  simp [chipLevel, canonical]

/-- Literal component selected by the explicit representative, pending its certification. -/
def C (m : ℕ) (i : ZMod n) : Set (SignedConfig n) := component (canonical m i).lift
noncomputable def r (n m : ℕ) [NeZero n] (i : ZMod n) : ℕ :=
  Nat.card {d : Config n // NatRecurrent d ∧ d.lift ∈ C m i}
noncomputable def testCount (n m : ℕ) [NeZero n] (i : ZMod n) : ℕ :=
  Nat.card {d : Config n // CycleTest d ∧ chipLevel d = m ∧ chipWeight d = i}

/- Exact remaining obligations, ordinary Prop definitions, not postulated facts. -/
def CycleTestBridge : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : Config n, NatRecurrent c ↔ CycleTest c

def CanonicalTest : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ i : ZMod n,
    CycleTest (canonical m i) ∧ chipWeight (canonical m i) = i

/-- Direct cycle-specific substitute for the source's torsion-group uniqueness route. -/
def ConnectedFibres : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ a b : Config n,
    NatRecurrent a → NatRecurrent b →
    chipLevel a = chipLevel b → chipWeight a = chipWeight b → Related a.lift b.lift

def RotationCount : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ i : ZMod n,
    testCount n m (i + m) = testCount n m i

def UnitCount : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ (u : (ZMod n)ˣ) (i : ZMod n),
    testCount n m ((u : ZMod n) * i) = testCount n m i

def ArithmeticOrbit : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ i j : ZMod n,
    Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val →
    ∃ (u : (ZMod n)ˣ) (b : ℕ), j = (u : ZMod n) * i + (b * m : ℕ)

/-- U, conditional on the three explicitly named semantic obligations. -/
theorem unique_component_conditional (hc : CycleTestBridge) (ha : CanonicalTest)
    (hu : ConnectedFibres) (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m)
    (i : ZMod n) :
    NatRecurrent (canonical m i) ∧ chipLevel (canonical m i) = m ∧
    chipWeight (canonical m i) = i ∧
    ∀ d : Config n, NatRecurrent d →
      (d.lift ∈ C m i ↔ chipLevel d = m ∧ chipWeight d = i) := by
  have hcan := ha n m hn hm i
  have hrec := (hc n hn _).mpr hcan.1
  refine ⟨hrec, canonical_level m i, hcan.2, ?_⟩
  intro d hd
  constructor
  · intro h
    have hl := level_related h
    have hw := weight_related h
    change level (canonical m i).lift = level d.lift at hl
    rw [level_lift, level_lift, canonical_level] at hl
    exact ⟨by exact_mod_cast hl.symm, hw.symm.trans hcan.2⟩
  · rintro ⟨hl, hw⟩
    exact hu n hn _ _ hrec hd ((canonical_level m i).trans hl.symm) (hcan.2.trans hw.symm)

theorem r_eq_testCount_conditional (hc : CycleTestBridge) (ha : CanonicalTest)
    (hu : ConnectedFibres) (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m)
    (i : ZMod n) : r n m i = testCount n m i := by
  have h := (unique_component_conditional hc ha hu n m hn hm i).2.2.2
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro d
  constructor
  · rintro ⟨hr, hd⟩
    exact ⟨(hc n hn d).mp hr, (h d hr).mp hd⟩
  · rintro ⟨hr, hl, hw⟩
    have hd := (hc n hn d).mpr hr
    exact ⟨hd, (h d hd).mpr ⟨hl, hw⟩⟩

/-- CONDITIONAL MathDB 338887. All six hypotheses are unproved obligations. -/
theorem mathdb_338887_conditional (hc : CycleTestBridge) (ha : CanonicalTest)
    (hu : ConnectedFibres) (hr : RotationCount) (hv : UnitCount) (ho : ArithmeticOrbit)
    (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m) (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) : r n m i = r n m j := by
  rw [r_eq_testCount_conditional hc ha hu n m hn hm i,
    r_eq_testCount_conditional hc ha hu n m hn hm j]
  obtain ⟨u, b, rfl⟩ := ho n m hn hm i j h
  have hb : ∀ b : ℕ, ∀ y : ZMod n,
      testCount n m (y + (b * m : ℕ)) = testCount n m y := by
    intro b
    induction b with
    | zero => intro y; simp
    | succ b ih =>
      intro y
      have he : (y + ((b+1)*m : ℕ) : ZMod n) = (y + (b*m : ℕ)) + m := by
        push_cast; ring
      rw [he, hr n m hn hm, ih]
  rw [hb, hv n m hn hm]
end ChanLevine

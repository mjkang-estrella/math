import Cardinality
namespace ChanLevine
/-- Round 1 handback only: seven explicit premises remain unproved. -/
theorem mathdb_338887_conditional_full
    (hc : CycleTestBridge) (ha : CanonicalTest) (hu : ConnectedFibres)
    (hr : RotationCount) (hv : UnitCount) (ho : ArithmeticOrbit) (hs : AmbientBridge)
    (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m) (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    (∃! S : Set (SignedConfig n), ∃ a : Config n,
      NatRecurrent a ∧ chipLevel a = m ∧ chipWeight a = i ∧ S = component a.lift) ∧
    RecurrentComponent (C m i) ∧ r n m i = r n m j := by
  have hp := mathdb_338887_package_conditional hc ha hu hr hv ho hs n m hn hm i j h
  exact ⟨existsUnique_component_conditional hc ha hu n m hn hm i, hp.1, hp.2.2.2⟩
end ChanLevine

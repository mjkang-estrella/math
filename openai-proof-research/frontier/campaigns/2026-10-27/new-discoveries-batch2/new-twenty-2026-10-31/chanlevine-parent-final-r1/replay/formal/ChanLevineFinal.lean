import Endpoint
import SemFinal4
import CountFinal
import CountFinal5
import CountR7CFinal
import CountR7TFinal

namespace ChanLevine

/-- Chan–Levine Conjecture 8.3, with the source component existence and uniqueness. -/
theorem mathdb_338887 (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m)
    (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    (∃! S : Set (SignedConfig n), ∃ a : Config n,
      NatRecurrent a ∧ chipLevel a = m ∧ chipWeight a = i ∧ S = component a.lift) ∧
    RecurrentComponent (C m i) ∧ r n m i = r n m j := by
  exact mathdb_338887_conditional_full
    Sem5.cycleTestBridge canonicalTest Sem5.connectedFibres rotationCount
    (Round6.unitCount Round7C.matchingCountConvolution Round7T.matchingTraceExpansion)
    arithmeticOrbit Sem3.ambientBridge_unconditional n m hn hm i j h

/-- At positive level the recurrent component cardinality depends only on the gcd. -/
theorem recurrent_count_depends_only_on_gcd (n m : ℕ) [NeZero n]
    (hn : 3 ≤ n) (hm : 1 ≤ m) (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    r n m i = r n m j :=
  (mathdb_338887 n m hn hm i j h).2.2

#print axioms mathdb_338887
#print mathdb_338887
#print axioms recurrent_count_depends_only_on_gcd
end ChanLevine

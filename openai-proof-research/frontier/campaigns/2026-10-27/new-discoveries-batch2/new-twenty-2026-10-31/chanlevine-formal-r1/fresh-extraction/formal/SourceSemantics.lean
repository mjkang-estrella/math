import Reduction
namespace ChanLevine
variable {n : ℕ} [NeZero n]

/-- Natural-chip processing with the same advance-then-move convention. -/
def Config.fire (c : Config n) (v : ZMod n) : Config n :=
  ⟨fun k => c.x k - (if k = v then 1 else 0) +
    (if k = target c.lift v then 1 else 0), Function.update c.q v (!c.q v)⟩

omit [NeZero n] in
theorem Config.lift_fire (c : Config n) (v : ZMod n) (hv : 0 < c.x v) :
    (c.fire v).lift = ChanLevine.fire c.lift v := by
  cases c with
  | mk x q =>
    change 0 < x v at hv
    dsimp [Config.fire, Config.lift, ChanLevine.fire, target]
    congr 1
    funext k
    by_cases hk : k = v
    · subst k
      simp only [ite_true]
      rw [Int.ofNat_sub (by omega : 1 ≤ x v)]
      split_ifs <;> simp
    · simp only [hk, ite_false, Nat.sub_zero, sub_zero]
      split_ifs <;> simp

/-- Source Definition 4.8: a diverse infinite forward legal walk within a set. -/
def DiverseWalkIn (S : Set (SignedConfig n)) : Prop :=
  ∃ (c : ℕ → SignedConfig n) (a : ℕ → ZMod n),
    (∀ t, c t ∈ S) ∧
    (∀ t, 0 < (c t).x (a t) ∧ c (t+1) = fire (c t) (a t)) ∧
    ∀ v T, ∃ t, T ≤ t ∧ a t = v

def DiverseBackwardWalkIn (S : Set (SignedConfig n)) : Prop :=
  ∃ (c : ℕ → SignedConfig n) (a : ℕ → ZMod n),
    (∀ t, c t ∈ S) ∧
    (∀ t, 0 < (c (t+1)).x (a t) ∧ c t = fire (c (t+1)) (a t)) ∧
    ∀ v T, ∃ t, T ≤ t ∧ a t = v

def DiverseTwoSidedWalkIn (S : Set (SignedConfig n)) : Prop :=
  ∃ (c : ℤ → SignedConfig n) (a : ℤ → ZMod n),
    (∀ t, c t ∈ S) ∧
    (∀ t, 0 < (c t).x (a t) ∧ c (t+1) = fire (c t) (a t)) ∧
    ∀ v, Set.Infinite {t | a t = v}

def RecurrentComponent (S : Set (SignedConfig n)) : Prop :=
  (∃ c, S = component c) ∧
    (DiverseWalkIn S ∨ DiverseBackwardWalkIn S ∨ DiverseTwoSidedWalkIn S)

/-- Remaining source-facing obligations beyond the nonnegative counting domain. -/
def AmbientBridge : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n →
    (∀ c : SignedConfig n, Recurrent c → ∀ k, 0 ≤ c.x k) ∧
    (∀ c : SignedConfig n, Recurrent c → RecurrentComponent (component c))

/-- Full source-facing conditional package. No unconditional conjecture is asserted. -/
theorem mathdb_338887_package_conditional
    (hc : CycleTestBridge) (ha : CanonicalTest) (hu : ConnectedFibres)
    (hr : RotationCount) (hv : UnitCount) (ho : ArithmeticOrbit) (hs : AmbientBridge)
    (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m) (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    RecurrentComponent (C m i) ∧
    (∀ c : SignedConfig n, Recurrent c → ∀ k, 0 ≤ c.x k) ∧
    (NatRecurrent (canonical m i) ∧ chipLevel (canonical m i) = m ∧
      chipWeight (canonical m i) = i ∧
      ∀ d : Config n, NatRecurrent d →
        (d.lift ∈ C m i ↔ chipLevel d = m ∧ chipWeight d = i)) ∧
    r n m i = r n m j := by
  have hu' := unique_component_conditional hc ha hu n m hn hm i
  exact ⟨(hs n hn).2 _ hu'.1, (hs n hn).1, hu',
    mathdb_338887_conditional hc ha hu hr hv ho n m hn hm i j h⟩
end ChanLevine

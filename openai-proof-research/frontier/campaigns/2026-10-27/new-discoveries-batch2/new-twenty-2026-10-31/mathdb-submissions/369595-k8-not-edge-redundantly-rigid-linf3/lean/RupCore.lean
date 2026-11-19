/-!
# A small reverse-unit-propagation (RUP) checker with a soundness proof

Literals are natural numbers: the literal `2 * v` is the positive literal of the
variable `v` and `2 * v + 1` is its negation.  A clause is a list of literals.
An assignment is a map `Nat → Bool` on variables.

`rupCheck C Hs` assumes the negation of every literal of `C` and then runs unit
propagation through the hint clauses `Hs`, in order.  Every hint must be either
unit (exactly one literal not yet falsified, and no literal already true) or
conflicting (all literals falsified).  The check succeeds when a conflict is
reached.  Soundness (`rupCheck_sound`): if an assignment satisfies every hint
clause, then it satisfies `C`.

The checker is an ordinary Lean function.  Certificates are checked by kernel
reduction (`decide +kernel`), which introduces no axioms.
-/

namespace Rup

abbrev Clause := List Nat

/-- Value of a literal under an assignment of the variables. -/
def litVal (α : Nat → Bool) (l : Nat) : Bool := α (l >>> 1) ^^ l.testBit 0

/-- A clause is satisfied when one of its literals is true. -/
def Sat (α : Nat → Bool) (C : Clause) : Prop := C.any (litVal α) = true

/-- All clauses of a list are satisfied.  An inductive predicate, so proofs are
built by explicit constructor applications. -/
inductive AllSat (α : Nat → Bool) : List Clause → Prop
  | nil : AllSat α []
  | cons {C : Clause} {Cs : List Clause} : Sat α C → AllSat α Cs → AllSat α (C :: Cs)

/-- Outcome of examining one hint clause against the current trail. -/
inductive Hint where
  | bad
  | conflict
  | unit (l : Nat)

/-- `classify t H pend`: `t` is the trail (bit `l` set means literal `l` is
assumed true).  `pend` is the unique unfalsified literal found so far. -/
def classify (t : Nat) : Clause → Option Nat → Hint
  | [], none => .conflict
  | [], some l => .unit l
  | l :: rest, pend =>
    if t.testBit l then .bad
    else if t.testBit (l ^^^ 1) then classify t rest pend
    else match pend with
      | none => classify t rest (some l)
      | some _ => .bad

/-- Unit propagation through the hints. -/
def runHints (t : Nat) : List Clause → Bool
  | [] => false
  | H :: Hs =>
    match classify t H none with
    | .bad => false
    | .conflict => true
    | .unit l => runHints (t ||| (1 <<< l)) Hs

/-- Initial trail: the negations of the literals of the clause. -/
def initTrail : Clause → Nat → Nat
  | [], t => t
  | l :: rest, t => initTrail rest (t ||| (1 <<< (l ^^^ 1)))

def rupCheck (C : Clause) (Hs : List Clause) : Bool := runHints (initTrail C 0) Hs

/-! ## Soundness -/

theorem testBit_setLit (t l m : Nat) :
    (t ||| (1 <<< l)).testBit m = (t.testBit m || decide (l = m)) := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem shift_xor_one (l : Nat) : (l ^^^ 1) >>> 1 = l >>> 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_xor]
  have : (1 : Nat).testBit (1 + i) = false := by
    rw [Nat.add_comm, Nat.testBit_succ]; simp
  rw [this, Bool.xor_false]

theorem testBit0_xor_one (l : Nat) : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
  rw [Nat.testBit_xor]
  have : (1 : Nat).testBit 0 = true := by decide
  rw [this, Bool.xor_true]

theorem litVal_neg (α : Nat → Bool) (l : Nat) : litVal α (l ^^^ 1) = !litVal α l := by
  unfold litVal
  rw [shift_xor_one, testBit0_xor_one]
  cases α (l >>> 1) <;> cases l.testBit 0 <;> rfl

/-- Trail invariant: every literal on the trail is true. -/
def Inv (α : Nat → Bool) (t : Nat) : Prop := ∀ m, t.testBit m = true → litVal α m = true

theorem Inv.set {α : Nat → Bool} {t l : Nat} (h : Inv α t) (hl : litVal α l = true) :
    Inv α (t ||| (1 <<< l)) := by
  intro m hm
  rw [testBit_setLit] at hm
  rcases Bool.or_eq_true_iff.mp hm with hm | hm
  · exact h m hm
  · have : l = m := of_decide_eq_true hm
    subst this; exact hl

theorem classify_sound {α : Nat → Bool} {t : Nat} (ht : Inv α t) :
    ∀ (H : Clause) (pend : Option Nat),
      (H.any (litVal α) = true ∨ ∃ p, pend = some p ∧ litVal α p = true) →
      match classify t H pend with
      | .bad => True
      | .conflict => False
      | .unit l => litVal α l = true
  | [], none, h => by
    rcases h with h | ⟨p, hp, _⟩
    · simp at h
    · cases hp
  | [], some l, h => by
    rcases h with h | ⟨p, hp, hpv⟩
    · simp at h
    · cases hp; exact hpv
  | l :: rest, pend, h => by
    unfold classify
    by_cases h1 : t.testBit l = true
    · simp [h1]
    · simp only [h1]
      by_cases h2 : t.testBit (l ^^^ 1) = true
      · simp only [h2, ite_true, Bool.false_eq_true, ite_false]
        apply classify_sound ht rest pend
        have hfalse : litVal α l = false := by
          have := ht _ h2
          rw [litVal_neg] at this
          simpa using this
        rcases h with h | h
        · left
          rw [List.any_cons, hfalse, Bool.false_or] at h
          exact h
        · right; exact h
      · simp only [h2, Bool.false_eq_true, ite_false]
        cases pend with
        | none =>
          apply classify_sound ht rest (some l)
          rcases h with h | ⟨p, hp, _⟩
          · rw [List.any_cons] at h
            rcases Bool.or_eq_true_iff.mp h with h | h
            · right; exact ⟨l, rfl, h⟩
            · left; exact h
          · cases hp
        | some _ => trivial

theorem runHints_sound {α : Nat → Bool} :
    ∀ (Hs : List Clause) (t : Nat), Inv α t → AllSat α Hs → runHints t Hs = true → False
  | [], _, _, _, h => by simp [runHints] at h
  | H :: Hs, t, ht, hall, h => by
    cases hall with
    | cons hH hHs =>
      have key := classify_sound ht H none (Or.inl hH)
      unfold runHints at h
      revert key h
      cases classify t H none with
      | bad => intro _ h; simp at h
      | conflict => intro key _; exact key
      | unit l =>
        intro key h
        exact runHints_sound Hs _ (ht.set key) hHs h

theorem initTrail_inv {α : Nat → Bool} :
    ∀ (C : Clause) (t : Nat), Inv α t → C.any (litVal α) = false → Inv α (initTrail C t)
  | [], _, ht, _ => ht
  | l :: rest, t, ht, hC => by
    rw [List.any_cons, Bool.or_eq_false_iff] at hC
    apply initTrail_inv rest _ _ hC.2
    apply ht.set
    rw [litVal_neg, hC.1]; rfl

theorem rupCheck_sound {α : Nat → Bool} {C : Clause} {Hs : List Clause}
    (hchk : rupCheck C Hs = true) (hs : AllSat α Hs) : Sat α C := by
  unfold Sat
  cases hC : C.any (litVal α) with
  | true => rfl
  | false =>
    exfalso
    have h0 : Inv α 0 := by
      intro m hm
      rw [Nat.zero_testBit] at hm
      cases hm
    exact runHints_sound Hs _ (initTrail_inv C 0 h0 hC) hs hchk

/-- The empty clause is never satisfied. -/
theorem not_sat_nil (α : Nat → Bool) : ¬ Sat α [] := by
  simp [Sat]

end Rup

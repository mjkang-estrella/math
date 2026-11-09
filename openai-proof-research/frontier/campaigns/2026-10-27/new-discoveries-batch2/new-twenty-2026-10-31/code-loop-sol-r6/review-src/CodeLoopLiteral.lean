import CodeLoopClasses
import CodeLoopSigns

noncomputable section

/-- The four factor axioms, in additive sign notation, for every codeword. -/
structure BinaryFactor {α : Type} [Fintype α] (V : Submodule (ZMod 2) (α → ZMod 2)) where
  f : V → V → ZMod 2
  diagonal : ∀ v, f v v = ((wordWeight v.val / 4 : Nat) : ZMod 2)
  symmetry : ∀ v w, f v w + f w v = ((pairWeight v.val w.val / 2 : Nat) : ZMod 2)
  zero_left : ∀ v, f 0 v = 0
  zero_right : ∀ v, f v 0 = 0
  coboundary : ∀ u v w, f u v + f (u+v) w + f v w + f u (v+w) =
    (tripleWeight u.val v.val w.val : ZMod 2)

def BinaryFactor.mul {α : Type} [Fintype α] {V : Submodule (ZMod 2) (α → ZMod 2)}
    (F : BinaryFactor V) (a b : ZMod 2 × V) : ZMod 2 × V :=
  (a.1+b.1+F.f a.2 b.2,a.2+b.2)

/-- All structural loop axioms are stated explicitly rather than assumed from factor sets. -/
def IsMoufangLoop (L : Type) (mul : L → L → L) : Prop :=
  (∃ one, (∀ a, mul one a = a) ∧ (∀ a, mul a one = a)) ∧
  (∀ a c, ∃! b, mul a b = c) ∧ (∀ a c, ∃! b, mul b a = c) ∧
  (∀ a b c, mul (mul a b) (mul c a) = mul a (mul (mul b c) a))

def Represents {α : Type} [Fintype α] {V : Submodule (ZMod 2) (α → ZMod 2)}
    (F : BinaryFactor V) (L : Type) (mul : L → L → L) : Prop :=
  ∃ e : L ≃ (ZMod 2 × V), ∀ a b, e (mul a b) = F.mul (e a) (e b)

/-- Literal 2019 universal uniqueness assertion, with reduced representations.
Finite coordinate types carry their proved degree and are equivalent to standard Fin coordinates.
No minimality, rank bound, or center-order restriction is added. -/
def Literal2019Uniqueness : Prop :=
  ∀ (α β : Type) (_ : Fintype α) (_ : Fintype β)
    (V : Submodule (ZMod 2) (α → ZMod 2)) (W : Submodule (ZMod 2) (β → ZMod 2))
    (F : BinaryFactor V) (G : BinaryFactor W)
    (qV : Fintype (Quotient (binaryCodeSetoid V)))
    (qW : Fintype (Quotient (binaryCodeSetoid W)))
    (pV : ∀ q, Fintype (binaryClassPositions V q))
    (pW : ∀ q, Fintype (binaryClassPositions W q)),
    (∀ v : V, wordWeight v.val % 4 = 0) →
    (∀ w : W, wordWeight w.val % 4 = 0) →
    (∀ q, @Fintype.card _ (pV q) < 8) →
    (∀ q, @Fintype.card _ (pW q) < 8) →
    ∀ (L : Type) (mul : L → L → L), IsMoufangLoop L mul →
    Represents F L mul → Represents G L mul →
    Fintype.card α = Fintype.card β →
    binaryCodeType V qV pV = binaryCodeType W qW pW →
    ∃ e : α ≃ β, ∀ v, v ∈ V ↔ (fun c => v (e.symm c)) ∈ W

def witnessFactor (i : Fin 2) : BinaryFactor (D i) where
  f := codeFactor i
  diagonal := codeFactor_diagonal i
  symmetry := codeFactor_symmetry i
  zero_left := codeFactor_zero_left i
  zero_right := codeFactor_zero_right i
  coboundary := codeFactor_coboundary i

theorem common_isMoufangLoop : IsMoufangLoop CommonLoop commonMul :=
  ⟨⟨commonOne,common_one_mul,common_mul_one⟩,common_left_division,
    common_right_division,common_moufang⟩

theorem witness_represents (i : Fin 2) : Represents (witnessFactor i) CommonLoop commonMul :=
  ⟨representationEquiv i,representation_multiplicative i⟩

theorem literal2019_refuted : ¬ Literal2019Uniqueness := by
  intro h
  apply D_no_coordinate_equivalence
  apply h (Dcoord 0) (Dcoord 1) inferInstance inferInstance (D 0) (D 1)
    (witnessFactor 0) (witnessFactor 1)
    (columnClassFintype 0) (columnClassFintype 1)
    (classPositionsFintype 0)
    (classPositionsFintype 1)
    (D_doubly_even 0) (D_doubly_even 1) (D_reduced 0) (D_reduced 1)
    CommonLoop commonMul common_isMoufangLoop (witness_represents 0) (witness_represents 1)
  · rw [dcoord_card,dcoord_card]
  · change codeType 0 = codeType 1
    rw [exact_codeType,exact_codeType]

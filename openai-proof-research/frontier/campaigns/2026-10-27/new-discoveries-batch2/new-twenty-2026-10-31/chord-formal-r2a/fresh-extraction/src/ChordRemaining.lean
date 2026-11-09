import ChordSmall
namespace Chord

/-- A sub-diagram retains an order-preserving set of endpoints closed under pairing. -/
structure Subdiagram {k n} (A : Diagram k) (D : Diagram n) where
  positions : Fin (2*k) → Fin (2*n)
  increasing : StrictMono positions
  closed : ∀ i, D.partner (positions i) = positions (A.partner i)

def restrictSides {k n} {A : Diagram k} {D : Diagram n}
    (S : Subdiagram A D) (c : Sides n) : Sides k := c ∘ S.positions

def Crosses {n} (D : Diagram n) (a b : Fin (2*n)) : Prop :=
  a < D.partner a ∧ b < D.partner b ∧
  ((a < b ∧ b < D.partner a ∧ D.partner a < D.partner b) ∨
   (b < a ∧ a < D.partner b ∧ D.partner b < D.partner a))

def HasTriangle {n} (D : Diagram n) : Prop :=
  ∃ a b c, Crosses D a b ∧ Crosses D a c ∧ Crosses D b c

def Bipartite {n} (D : Diagram n) : Prop :=
  ∃ color : Fin (2*n) → Bool,
    (∀ i, color (D.partner i) = color i) ∧
    ∀ a b, Crosses D a b → color a ≠ color b

def MaxTwo {n} (D : Diagram n) : Prop := ∀ g, genusRange D g → g ≤ 2

def FiveProperty (D : Diagram 5) : Prop :=
  (∃ a, a < D.partner a ∧ ∀ b, ¬Crosses D a b ∧ ¬Crosses D b a) ∧
  (HasTriangle D → Equivalent D (r3Block 5 (by decide)))

/-- Exact outstanding first-return theorem, including both empty circles. -/
def DartBridge : Prop := ∀ n (D : Diagram n) c, boundary D c = dartBoundary D c

/-- Orbit tracing must be proved to be the mathematical permutation face count. -/
def OrbitCounterCorrect : Prop := ∀ size (f : Fin size ≃ Fin size),
  cycles size (fun i => if h : i < size then (f ⟨i,h⟩).val else i) =
    (Finset.univ.filter (fun i : Fin size =>
      ∀ k : Fin (size+1), i ≤ (Nat.rec i (fun _ x => f x) k.val))).card

def FacePermutationCorrect : Prop := ∀ n (D : Diagram n) c,
  ∃ f : Fin (6*n) ≃ Fin (6*n), ∀ i, (f i).val = face D c i.val

/-- Existence/integrality is stated by an equation; no floor division is used. -/
def EulerRealization : Prop := ∀ n (D : Diagram n) c, ∃ g, HasGenus D c g

def Deletion : Prop := ∀ n (D : Diagram (n+1)) (A : Diagram n)
  (S : Subdiagram A D) c,
  boundary A (restrictSides S c) = boundary D c+1 ∨
  boundary A (restrictSides S c)+1 = boundary D c

def Heredity : Prop := ∀ k n (A : Diagram k) (D : Diagram n),
  Subdiagram A D → MaxTwo D → MaxTwo A

def BipartitePlanarity : Prop := ∀ n (D : Diagram n), Bipartite D → genusRange D 0

def FiveChordLemma : Prop := ∀ D : Diagram 5, MaxTwo D → FiveProperty D

/-- The shortest-odd-cycle argument, after planarity and five-chord obstruction. -/
def TriangleReduction : Prop := ∀ n, 3 ≤ n → ∀ D : Diagram n,
  ¬genusRange D 0 →
  (∀ A : Diagram 5, Subdiagram A D → FiveProperty A) → HasTriangle D

/-- The remaining pair/arc/adjacency/rotation argument, including n=3. -/
def TriangleRigidity : Prop := ∀ n (hn : 3 ≤ n), n ≠ 4 → ∀ D : Diagram n,
  HasTriangle D →
  (∀ A : Diagram 5, Subdiagram A D → FiveProperty A) →
  Equivalent D (r3Block n hn)

/-- Inductive end-edge transfer lemma, still unproved. -/
def RepresentativeExistence : Prop := ∀ n (hn : 3 ≤ n), Range12 (r3Block n hn)

/-- Exact finite enumeration target; equivalence is the literal setoid. -/
def ExactlyClasses (n count : Nat) : Prop := ∃ reps : Fin count → Diagram n,
  (∀ i, Range12 (reps i)) ∧
  (∀ i j, Equivalent (reps i) (reps j) → i=j) ∧
  (∀ D : Diagram n, Range12 D → ∃ i, Equivalent D (reps i))

def FourChordEnumeration : Prop := ExactlyClasses 4 4

def RemainingModel : Prop := DartBridge ∧ OrbitCounterCorrect ∧ FacePermutationCorrect ∧ EulerRealization
end Chord

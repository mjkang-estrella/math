import ChordComb2Final
namespace Chord.Comb4
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- Old sides when the last adjacent pair is removed. -/
def oldSides {n} (c : Sides (n+1)) : Sides n :=
  fun i => c ⟨i.val, by omega⟩

/-- Two choices on the appended chord; old endpoint numbers are unchanged. -/
def appendSides {n} (c : Sides n) (p q : Bool) : Sides (n+1) :=
  fun i => if h : i.val < 2*n then c ⟨i.val,h⟩ else if i.val = 2*n then p else q

theorem old_append {n} (c : Sides n) (p q : Bool) :
    oldSides (appendSides c p q) = c := by
  funext i
  simp [oldSides, appendSides, i.isLt]

theorem append_old {n} (c : Sides (n+1)) :
    appendSides (oldSides c) (c ⟨2*n, by omega⟩) (c ⟨2*n+1, by omega⟩) = c := by
  funext i
  unfold appendSides oldSides
  split
  · rfl
  · split
    · congr 1; apply Fin.ext; dsimp; omega
    · congr 1; apply Fin.ext; have := i.isLt; dsimp at *; omega

/-- Face reachability between the two half-edges of the end edge, in the
actual frozen 6n model. No quotient or replacement boundary count is used. -/
def EndSame (n : Nat) (hn : 3 ≤ n) (c : Sides n) : Prop :=
  0 ∈ trace (face (r3Block n hn) c) (6*n) (3*(2*n-1)+1) []

instance (n) (hn : 3 ≤ n) (c : Sides n) : Decidable (EndSame n hn c) :=
  inferInstanceAs (Decidable (0 ∈ trace _ _ _ _))

/-- The three admissible states are (b=n-2,same), (b=n,same),
and (b=n,different). This avoids subtraction in the invariant. -/
def EndInvariant (n : Nat) (hn : 3 ≤ n) (c : Sides n) : Prop :=
  (boundary (r3Block n hn) c + 2 = n ∧ EndSame n hn c) ∨
  boundary (r3Block n hn) c = n

/-- Kernel check of all 64 base assignments, including the end-face condition. -/
theorem endInvariant_three : ∀ c : Sides 3, EndInvariant 3 (by decide) c := by
  unfold EndInvariant EndSame
  decide

/-- UNPROVED SURGERY OBLIGATION. This is a stronger, face-sensitive replacement
for RepresentativeStep, exposed as a Prop and never asserted as a theorem.
Equal attachment sides add one face and preserve end-face connectivity.
Opposite sides split/merge the two end faces and make the new end edge single. -/
def EndEdgeSurgery : Prop := ∀ n (hn : 3 ≤ n) (c : Sides n) (p q : Bool),
  let D := r3Block n hn
  let E := r3Block (n+1) (by omega)
  let e := appendSides c p q
  if p = q then
    boundary E e = boundary D c + 1 ∧
      (EndSame (n+1) (by omega) e ↔ EndSame n hn c)
  else
    (if EndSame n hn c then boundary E e = boundary D c + 1
      else boundary E e + 1 = boundary D c) ∧
      EndSame (n+1) (by omega) e

theorem invariant_append (surgery : EndEdgeSurgery) {n} (hn : 3 ≤ n)
    (c : Sides n) (h : EndInvariant n hn c) (p q : Bool) :
    EndInvariant (n+1) (by omega) (appendSides c p q) := by
  have hs := surgery n hn c p q
  dsimp only at hs
  unfold EndInvariant at h ⊢
  by_cases hp : p = q
  · subst p
    simp only [↓reduceIte] at hs
    rcases h with ⟨hb,he⟩ | hb
    · exact Or.inl ⟨by omega, hs.2.mpr he⟩
    · exact Or.inr (by omega)
  · simp only [hp, ↓reduceIte] at hs
    by_cases he : EndSame n hn c
    · simp only [he, ↓reduceIte] at hs
      rcases h with ⟨hb,_⟩ | hb
      · exact Or.inl ⟨by omega, hs.2⟩
      · exact Or.inr (by omega)
    · simp only [he, ↓reduceIte] at hs
      rcases h with ⟨_,he'⟩ | hb
      · exact False.elim (he he')
      · exact Or.inl ⟨by omega, hs.2⟩

theorem invariant_all (surgery : EndEdgeSurgery) (n) (hn : 3 ≤ n) :
    ∀ c, EndInvariant n hn c := by
  induction n, hn using Nat.le_induction with
  | base => exact endInvariant_three
  | succ n hn ih =>
    intro c
    rw [← append_old c]
    exact invariant_append surgery hn _ (ih _) _ _

/-- All-in extensions preserve each witnessed genus, with the surgery hypothesis explicit. -/
theorem genus_append_equal (surgery : EndEdgeSurgery) {n} (hn : 3 ≤ n)
    (c : Sides n) (p : Bool) (g : Nat) :
    HasGenus (r3Block (n+1) (by omega)) (appendSides c p p) g ↔
      HasGenus (r3Block n hn) c g := by
  have hs := surgery n hn c p p
  simp only [↓reduceIte] at hs
  unfold HasGenus
  rw [hs.1]
  omega

/-- The full RepresentativeExistence follows from the precise surgery obligation;
this does not claim to discharge that obligation. -/
theorem existence_of_surgery (surgery : EndEdgeSurgery) : RepresentativeExistence := by
  intro n hn
  have hw : genusRange (r3Block n hn) 1 ∧ genusRange (r3Block n hn) 2 := by
    induction n, hn using Nat.le_induction with
    | base => exact ⟨(genusRange_r3 1).mpr (by omega), (genusRange_r3 2).mpr (by omega)⟩
    | succ n hn ih =>
      obtain ⟨⟨c,hc⟩,⟨d,hd⟩⟩ := ih
      exact ⟨⟨_, (genus_append_equal surgery hn c false 1).mpr hc⟩,
        ⟨_, (genus_append_equal surgery hn d false 2).mpr hd⟩⟩
  intro g
  constructor
  · rintro ⟨c,hc⟩
    have hi := invariant_all surgery n hn c
    unfold HasGenus at hc
    rcases hi with ⟨hb,_⟩ | hb <;> omega
  · rintro (rfl | rfl)
    · exact hw.1
    · exact hw.2

theorem step_of_surgery (surgery : EndEdgeSurgery) : Comb2.RepresentativeStep := by
  intro n hn _
  exact existence_of_surgery surgery (n+1) (by omega)
end Chord.Comb4

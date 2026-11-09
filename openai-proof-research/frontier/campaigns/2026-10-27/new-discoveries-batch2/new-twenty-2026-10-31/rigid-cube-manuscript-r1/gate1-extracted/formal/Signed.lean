import Cube
import Mathlib.Tactic
set_option autoImplicit false
namespace MathDB364205
abbrev Sign := {z : ℤ // z = -1 ∨ z = 1}
abbrev SignedCube (n : ℕ) := Fin n → Sign

def signEquiv : Bool ≃ Sign where
  toFun b := if b then ⟨1, Or.inr rfl⟩ else ⟨-1, Or.inl rfl⟩
  invFun z := decide (z.val = 1)
  left_inv b := by cases b <;> rfl
  right_inv z := by
    rcases z with ⟨z, hz⟩
    rcases hz with rfl | rfl <;> rfl

def cubeEquiv (n : ℕ) : Cube n ≃ SignedCube n :=
  Equiv.piCongrRight fun _ => signEquiv

def signedDist {n : ℕ} (x y : SignedCube n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

theorem dist_encoding {n : ℕ} (x y : Cube n) :
    signedDist (cubeEquiv n x) (cubeEquiv n y) = dist x y := by
  unfold signedDist dist
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  exact not_congr (signEquiv.injective.eq_iff)

def signedA : Finset (SignedCube 8) := A.image (cubeEquiv 8)

def SignedMaximalDiameter {n : ℕ} (S : Finset (SignedCube n)) (r : ℕ) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, signedDist x y ≤ r) ∧
  (∃ x ∈ S, ∃ y ∈ S, signedDist x y = r) ∧
  (∀ x, x ∉ S → ∃ y ∈ S, r < signedDist x y)
def SignedRigid {n : ℕ} (S : Finset (SignedCube n)) (r : ℕ) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, signedDist x y = r

theorem signedA_card : signedA.card = 34 := by
  rw [signedA, Finset.card_image_of_injective _ (cubeEquiv 8).injective, card_A]

theorem signedA_maximal : SignedMaximalDiameter signedA 5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    simpa only [dist_encoding] using pair_bound a ha b hb
  · obtain ⟨a, ha, b, hb, he⟩ := diameter_attained
    exact ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      _, Finset.mem_image.mpr ⟨b, hb, rfl⟩, by simpa only [dist_encoding] using he⟩
  · intro x hx
    let a := (cubeEquiv 8).symm x
    have ha : a ∉ A := by
      intro h
      apply hx
      exact Finset.mem_image.mpr ⟨a, h, (cubeEquiv 8).apply_symm_apply x⟩
    obtain ⟨b, hb, hdist⟩ := outside_A a ha
    refine ⟨cubeEquiv 8 b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    have h : x = cubeEquiv 8 a := ((cubeEquiv 8).apply_symm_apply x).symm
    rw [h, dist_encoding]
    exact hdist

theorem signedA_rigid : SignedRigid signedA 5 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hdist⟩ := rigid_A a ha
  exact ⟨cubeEquiv 8 b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, by simpa only [dist_encoding] using hdist⟩

def LiteralSourceClaim : Prop := ∀ n r : ℕ, r ≤ n →
  IsGreatest {s : ℕ | ∃ S : Finset (SignedCube n), SignedMaximalDiameter S r ∧ SignedRigid S r ∧ S.card = s} (2 ^ r)

theorem literal_source_refutation : ¬ LiteralSourceClaim := by
  intro h
  have hm : 34 ∈ {s : ℕ | ∃ S : Finset (SignedCube 8), SignedMaximalDiameter S 5 ∧ SignedRigid S 5 ∧ S.card = s} :=
    ⟨signedA, signedA_maximal, signedA_rigid, signedA_card⟩
  have := (h 8 5 (by decide)).2 hm
  norm_num at this
end MathDB364205
#print axioms MathDB364205.literal_source_refutation

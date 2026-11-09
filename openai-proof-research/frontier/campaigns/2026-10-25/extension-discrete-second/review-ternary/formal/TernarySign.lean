import Mathlib

namespace TernarySign

abbrev Ternary := ℝ → ℝ → ℝ → ℝ

def heap : Ternary := fun x y z => x - y + z

def TernaryAssociative (F : Ternary) : Prop :=
  ∀ a b c d e, F (F a b c) d e = F a (F b c d) e ∧
    F (F a b c) d e = F a b (F c d e)

def Idempotent (F : Ternary) : Prop := ∀ x, F x x x = x

def StrictlyCoordinateMonotone (F : Ternary) : Prop :=
  (∀ y z, StrictMono (fun x => F x y z)) ∧
  (∀ x z, StrictAnti (fun y => F x y z)) ∧
  (∀ x y, StrictMono (fun z => F x y z))

def Reducible (F : Ternary) : Prop :=
  ∃ G : ℝ → ℝ → ℝ, (∀ x y z, G (G x y) z = G x (G y z)) ∧ ∀ x y z, G (G x y) z = F x y z

def PrintedRepresentation (F : Ternary) : Prop :=
  ∃ g : ℝ ≃ ℝ, (Monotone g ∨ Antitone g) ∧
    ∀ a : Fin 3 → ℝ, F (a 0) (a 1) (a 2) =
      g.symm (∑ i : Fin 3, (-1 : ℝ)^(i.val + 1) * g (a i))

theorem heap_associative : TernaryAssociative heap := by
  intro a b c d e
  constructor <;> simp [heap] <;> ring

theorem heap_idempotent : Idempotent heap := by
  intro x
  simp [heap]

theorem heap_strictly_monotone : StrictlyCoordinateMonotone heap := by
  refine ⟨?_, ?_, ?_⟩
  · intro y z a b h
    dsimp [heap]
    linarith
  · intro x z a b h
    dsimp [heap]
    linarith
  · intro x y a b h
    dsimp [heap]
    linarith

theorem heap_not_reducible : ¬ Reducible heap := by
  rintro ⟨G, ha, hf⟩
  let c := G 0 0
  have hl : ∀ z, G c z = z := by
    intro z
    simpa [c, heap] using hf 0 0 z
  have hr : ∀ x, G x c = x := by
    intro x
    calc
      G x c = G (G x 0) 0 := (ha x 0 0).symm
      _ = x := by simpa [heap] using hf x 0 0
  have hx : ∀ x, x = c - x + c := by
    intro x
    have hh := hf c x c
    rw [hl, hr] at hh
    exact hh
  have h0 := hx 0
  have h1 := hx 1
  linarith

theorem printed_sign_sum (f : Fin 3 → ℝ) :
    (∑ i : Fin 3, (-1 : ℝ)^(i.val + 1) * f i) = -f 0 + f 1 - f 2 := by
  norm_num [Fin.sum_univ_succ]
  ring

theorem heap_no_arbitrary_bijection (g : ℝ ≃ ℝ) :
    ¬ ∀ a : Fin 3 → ℝ, heap (a 0) (a 1) (a 2) =
      g.symm (∑ i : Fin 3, (-1 : ℝ)^(i.val + 1) * g (a i)) := by
  intro hf
  have hz : ∀ x : ℝ, g x = 0 := by
    intro x
    have hh := congrArg g (hf (fun _ => x))
    rw [printed_sign_sum] at hh
    simp only [Equiv.apply_symm_apply, heap, sub_self, zero_add] at hh
    linarith
  have hbad : (0 : ℝ) = 1 := g.injective ((hz 0).trans (hz 1).symm)
  norm_num at hbad

theorem heap_no_printed_representation : ¬ PrintedRepresentation heap := by
  rintro ⟨g, _, hf⟩
  exact heap_no_arbitrary_bijection g hf

theorem source_sign_counterexample :
    TernaryAssociative heap ∧ Idempotent heap ∧
    StrictlyCoordinateMonotone heap ∧ ¬ Reducible heap ∧
    Odd (3 : ℕ) ∧ ¬ PrintedRepresentation heap := by
  exact ⟨heap_associative, heap_idempotent, heap_strictly_monotone,
    heap_not_reducible, by decide, heap_no_printed_representation⟩

end TernarySign

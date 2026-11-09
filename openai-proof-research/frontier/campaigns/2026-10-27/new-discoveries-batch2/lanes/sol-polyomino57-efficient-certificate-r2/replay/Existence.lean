import Bounds
import Mathlib.Data.Finset.Prod
set_option autoImplicit false
namespace Polyomino57

def normalizedSquare (n : ℕ) : Finset GridPoint :=
  ((Finset.range n).product (Finset.range n)).image
    (fun p : ℕ × ℕ => ((p.1 : ℤ),(p.2 : ℤ)))

theorem mem_normalizedSquare (n : ℕ) (p : GridPoint) :
    p ∈ normalizedSquare n ↔ 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < n := by
  simp only [normalizedSquare, Finset.mem_image]
  constructor
  · rintro ⟨⟨x,y⟩,hxy,he⟩
    have hxy' := Finset.mem_product.mp hxy
    have hx := Finset.mem_range.mp hxy'.1
    have hy := Finset.mem_range.mp hxy'.2
    cases he
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro h
    exact ⟨(p.1.toNat,p.2.toNat),Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      by ext <;> dsimp <;> omega⟩

theorem square_origin_path (n x y : ℕ) (hx : x < n) (hy : y < n) :
    Relation.ReflTransGen (Step (normalizedSquare n)) (0,0) ((x : ℤ),(y : ℤ)) := by
  have mem (a b : ℕ) (ha : a < n) (hb : b < n) :
      ((a : ℤ),(b : ℤ)) ∈ normalizedSquare n :=
    (mem_normalizedSquare _ _).mpr ⟨by omega,by omega,by omega,by omega⟩
  have hor : ∀ a : ℕ, a < n →
      Relation.ReflTransGen (Step (normalizedSquare n)) (0,0) ((a : ℤ),0) := by
    intro a
    induction a with
    | zero => intro _; exact .refl
    | succ a ih =>
      intro ha
      apply (ih (by omega)).tail
      exact ⟨mem a 0 (by omega) (by omega),mem (a+1) 0 ha (by omega),
        Or.inl ⟨by simp, rfl⟩⟩
  induction y with
  | zero => exact hor x hx
  | succ y ih =>
    apply (ih (by omega)).tail
    exact ⟨mem x y hx (by omega),mem x (y+1) hx hy,
      Or.inr (Or.inr (Or.inl ⟨rfl,by simp⟩))⟩

theorem normalizedSquare_connected (n : ℕ) (hn : 0 < n) :
    EdgeConnected (normalizedSquare n) := by
  have origin : (0,0) ∈ normalizedSquare n :=
    (mem_normalizedSquare _ _).mpr ⟨by omega,by omega,by omega,by omega⟩
  have path : ∀ p ∈ normalizedSquare n,
      Relation.ReflTransGen (Step (normalizedSquare n)) (0,0) p := by
    intro p hp
    have h := (mem_normalizedSquare _ _).mp hp
    have he : ((p.1.toNat : ℤ),(p.2.toNat : ℤ)) = p := by ext <;> dsimp <;> omega
    rw [← he]
    exact square_origin_path n _ _ (by omega) (by omega)
  have reverse : ∀ {p q : GridPoint},
      Relation.ReflTransGen (Step (normalizedSquare n)) p q →
      Relation.ReflTransGen (Step (normalizedSquare n)) q p := by
    intro p q h
    induction h with
    | refl => exact .refl
    | tail _ hxy ih => exact ih.head ⟨hxy.2.1,hxy.1,adj_symm hxy.2.2⟩
  exact ⟨⟨_,origin⟩,fun p hp q hq => (reverse (path p hp)).trans (path q hq)⟩

theorem normalizedSquare_universal (n : ℕ) (hn : 0 < n) :
    UniversalContainer n (normalizedSquare n) := by
  refine ⟨normalizedSquare_connected n hn,?_⟩
  intro P hP hc
  refine ⟨(-(lowerCorner P hP.1).1,-(lowerCorner P hP.1).2),?_⟩
  intro p hp
  have h := normalized_coordinate_bound hP p hp
  rw [hc] at h
  exact (mem_normalizedSquare _ _).mpr ⟨h.1,by omega,h.2.2.1,by omega⟩

theorem normalizedSquare_card (n : ℕ) : (normalizedSquare n).card = n*n := by
  rw [normalizedSquare, Finset.card_image_of_injective]
  · simp
  · intro a b he
    have he' := Prod.mk.inj he
    apply Prod.ext <;> dsimp at * <;> omega

theorem eligible_positive (n : ℕ) (hn : 0 < n) : EligibleSize n (n*n) :=
  ⟨normalizedSquare n,normalizedSquare_card n,normalizedSquare_universal n hn⟩

theorem minimumSize_realized (n : ℕ) (hn : 0 < n) : EligibleSize n (minimumSize n) := by
  classical
  have hex : ∃ m, EligibleSize n m := ⟨n*n,eligible_positive n hn⟩
  rw [minimumSize, dite_eq_left hex]
  exact Nat.find_spec hex

theorem minimumSize_is_least (n : ℕ) (hn : 0 < n) :
    EligibleSize n (minimumSize n) ∧ ∀ m, EligibleSize n m → minimumSize n ≤ m :=
  ⟨minimumSize_realized n hn,fun _ h => minimumSize_le h⟩
end Polyomino57

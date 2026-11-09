module
public import GridFinal2
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace Grid343536
open SimpleGraph
def sym8 (k : ℕ) : Fin 8 → (G k k ≃g G k k) :=
  ![1, rowFlip k k, colFlip k k, rowFlip k k * colFlip k k,
    transpose k k, rowFlip k k * transpose k k, colFlip k k * transpose k k,
    rowFlip k k * colFlip k k * transpose k k]
def subIndices : Fin 10 → List (Fin 8) :=
  ![[0], [0,3], [0,1], [0,2], [0,4], [0,7],
    [0,5,3,6], [0,1,2,3], [0,3,4,7], [0,1,2,3,4,5,6,7]]
def symTable : Fin 8 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],
    ![1,0,3,2,5,4,7,6],
    ![2,3,0,1,6,7,4,5],
    ![3,2,1,0,7,6,5,4],
    ![4,6,5,7,0,2,1,3],
    ![5,7,4,6,1,3,0,2],
    ![6,4,7,5,2,0,3,1],
    ![7,5,6,4,3,1,2,0]]
theorem symTable_closed : ∀ h : Fin 10, ∀ i ∈ subIndices h, ∀ j ∈ subIndices h,
    symTable i j ∈ subIndices h := by decide
theorem symTable_one : ∀ h : Fin 10, (0 : Fin 8) ∈ subIndices h := by decide
theorem symTable_inv : ∀ h : Fin 10, ∀ i ∈ subIndices h,
    ∃ j ∈ subIndices h, symTable i j = 0 ∧ symTable j i = 0 := by decide
theorem sym8_mul (k : ℕ) (hk : k = 2 ∨ k = 3) (i j : Fin 8) :
    sym8 k i * sym8 k j = sym8 k (symTable i j) := by
  rcases hk with rfl | rfl
  all_goals
    fin_cases i <;> fin_cases j <;> apply DFunLike.ext <;> intro x <;> obtain ⟨a,b⟩ := x <;> fin_cases a <;> fin_cases b <;> rfl
def explicitSubgroup (k : ℕ) (hk : k = 2 ∨ k = 3) (h : Fin 10) :
    Subgroup (G k k ≃g G k k) where
  carrier := {g | ∃ i ∈ subIndices h, g = sym8 k i}
  one_mem' := ⟨0, symTable_one h, rfl⟩
  mul_mem' := by
    rintro g f ⟨i,hi,rfl⟩ ⟨j,hj,rfl⟩
    exact ⟨symTable i j, symTable_closed h i hi j hj, sym8_mul k hk i j⟩
  inv_mem' := by
    rintro g ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hij,_⟩ := symTable_inv h i hi
    refine ⟨j,hj, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [sym8_mul k hk, hij]
    rfl
theorem sym8_injective (k : ℕ) (hk : k = 2 ∨ k = 3) : Function.Injective (sym8 k) := by
  have hd : ∀ i j : Fin 8, (∀ x, sym8 k i x = sym8 k j x) → i = j := by
    rcases hk with rfl | rfl <;> decide
  intro i j h
  exact hd i j (fun x => congrArg (fun g : G k k ≃g G k k => g x) h)

theorem explicitSubgroup_injective (k : ℕ) (hk : k = 2 ∨ k = 3) :
    Function.Injective (explicitSubgroup k hk) := by
  have hd : ∀ a b : Fin 10, (∀ i : Fin 8, i ∈ subIndices a ↔ i ∈ subIndices b) → a = b := by decide
  intro a b h
  apply hd a b
  intro i
  have hm (a : Fin 10) : sym8 k i ∈ explicitSubgroup k hk a ↔ i ∈ subIndices a := by
    constructor
    · rintro ⟨j,hj,he⟩
      exact (sym8_injective k hk he).symm ▸ hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  rw [← hm a, ← hm b, h]
end Grid343536

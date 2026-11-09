module
public import GridExceptionalPartitions
@[expose] public section
namespace Grid343536
def point2 : Fin 4 → Fin 2 × Fin 2 := ![(0,0),(0,1),(1,0),(1,1)]
def loc2 (x : Fin 2 × Fin 2) : Fin 4 := ⟨x.1.val * 2 + x.2.val, by omega⟩
def block2 (a : Fin 15) : Setoid (Fin 2 × Fin 2) := Setoid.ker (fun x => codes4 a (loc2 x))
theorem equitable2_complete (r : Setoid (Fin 2 × Fin 2)) :
    ∃ a, r = block2 a := by
  obtain ⟨a, ha⟩ := setoid4_complete (Setoid.comap point2 r)
  refine ⟨a, ?_⟩
  have hc : ∀ i j, r (point2 i) (point2 j) ↔ codes4 a i = codes4 a j := by
    intro i j
    exact Iff.of_eq (congrArg (fun s : Setoid (Fin 4) => s i j) ha)
  ext u v
  have h (x : Fin 2 × Fin 2) : point2 (loc2 x) = x := by
    obtain ⟨i,j⟩ := x
    fin_cases i <;> fin_cases j <;> rfl
  change r u v ↔ codes4 a (loc2 u) = codes4 a (loc2 v)
  exact (by simpa only [h] using hc (loc2 u) (loc2 v))
end Grid343536

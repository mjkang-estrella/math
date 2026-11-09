import RawClosure
import Literal
namespace RawIndex
open Delta153

def survivors (g : Graph) (x : Nat) := (verts g).filter (fun i => i != x)
@[simp] theorem mem_survivors {g x i} : i ∈ survivors g x ↔ i < g.length ∧ i ≠ x := by
  simp [survivors, verts]

def old (g : Graph) (x : Nat) (i : Fin (survivors g x).length) : Fin g.length :=
  ⟨(survivors g x)[i.val], (mem_survivors.mp (List.getElem_mem i.isLt)).1⟩

theorem old_ne (g : Graph) (x : Nat) (i : Fin (survivors g x).length) : (old g x i).val ≠ x :=
  (mem_survivors.mp (List.getElem_mem i.isLt)).2

theorem old_injective (g : Graph) (x : Nat) : Function.Injective (old g x) := by
  intro i j hij
  apply Fin.ext
  exact ((List.nodup_range (n := g.length)).filter _).eq_of_getElem_eq i.isLt j.isLt
    (congrArg Fin.val hij)

theorem old_surjective (g : Graph) (x : Nat) (v : Fin g.length) (hv : v.val ≠ x) :
    ∃ i, old g x i = v := by
  have hm : v.val ∈ survivors g x := mem_survivors.mpr ⟨v.isLt,hv⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨⟨i,hi⟩, Fin.ext he⟩

noncomputable def survivorEquiv (g : Graph) (x : Fin g.length) :
    Fin (survivors g x.val).length ≃ {v : Fin g.length // v ≠ x} :=
  Equiv.ofBijective (fun i => ⟨old g x.val i, fun h => old_ne g x.val i (congrArg Fin.val h)⟩)
    ⟨fun _ _ h => old_injective g x.val (congrArg Subtype.val h), by
      intro v
      obtain ⟨i,hi⟩ := old_surjective g x.val v.val (fun h => v.property (Fin.ext h))
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem reduce_length (g : Graph) (x : Nat) :
    (reduce g x).length = (survivors g x).length := by
  simp [reduce, survivors]

theorem reduce_edge (g : Graph) (x : Nat) (i j : Fin (survivors g x).length) :
    edge (reduce g x) i.val j.val = edge g (old g x i).val (old g x j).val +
      if (old g x i).val != (old g x j).val && edge g x (old g x i).val == 2 &&
        edge g x (old g x j).val == 2 then 1 else 0 := by
  change (((survivors g x).map (fun u => (survivors g x).map (fun v =>
    edge g u v + if u != v && edge g x u == 2 && edge g x v == 2 then 1 else 0)))[i.val]?.getD [])[j.val]?.getD 0 = _
  simp only [List.getElem?_map]
  rw [List.getElem?_eq_getElem i.isLt]
  simp only [Option.map_some, Option.getD_some, List.getElem?_map]
  rw [List.getElem?_eq_getElem j.isLt]
  rfl
end RawIndex

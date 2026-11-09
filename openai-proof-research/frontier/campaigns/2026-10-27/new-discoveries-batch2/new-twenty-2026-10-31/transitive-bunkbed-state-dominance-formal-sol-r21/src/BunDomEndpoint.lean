import BunDomFiber
import BunOldStable
namespace BunDom
open Bun Classical

theorem stf_at_source (n u : Nat) (w : Asg n u) : stf n u u w = startST n u w := by
  cases u with
  | zero => simp [stf]
  | succ j => simp [stf]

theorem source_bottom_mem (n u : Nat) (w : Asg n u) :
    u ∈ sval false (stf n u u w) := by
  rw [stf_at_source]
  simp [sval, startST]

theorem source_inequality (n u : Nat) :
    Fintype.card {w : Asg n u // u ∈ sval true (stf n u u w)} ≤
      Fintype.card {w : Asg n u // u ∈ sval false (stf n u u w)} := by
  apply Fintype.card_le_of_injective
    (fun w => (⟨w.1, source_bottom_mem n u w.1⟩ :
      {w : Asg n u // u ∈ sval false (stf n u u w)}))
  intro a b h
  apply Subtype.ext
  exact congrArg (fun w : {w : Asg n u // u ∈ sval false (stf n u u w)} => w.1) h
end BunDom

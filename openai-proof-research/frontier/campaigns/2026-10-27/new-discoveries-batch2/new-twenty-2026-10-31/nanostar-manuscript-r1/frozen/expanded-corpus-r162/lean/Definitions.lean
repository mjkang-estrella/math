import Mathlib.Data.Nat.Totient
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace R162
inductive Tree where
| leaf : Tree
| unary : Tree → Tree
| binary : Tree → Tree → Tree
| ternary : Tree → Tree → Tree → Tree
deriving DecidableEq
open Tree
def size : Tree → ℕ
| leaf => 1
| unary a => 1 + size a
| binary a b => 1 + size a + size b
| ternary a b c => 1 + size a + size b + size c
def edges : Tree → List (ℕ × ℕ)
| leaf => []
| unary a => (0,1) :: (edges a).map (fun (x,y) => (x+1,y+1))
| binary a b => [(0,1),(0,1+size a)] ++
    (edges a).map (fun (x,y) => (x+1,y+1)) ++
    (edges b).map (fun (x,y) => (x+1+size a,y+1+size a))
| ternary a b c => [(0,1),(0,1+size a),(0,1+size a+size b)] ++
    (edges a).map (fun (x,y) => (x+1,y+1)) ++
    (edges b).map (fun (x,y) => (x+1+size a,y+1+size a)) ++
    (edges c).map (fun (x,y) => (x+1+size a+size b,y+1+size a+size b))
def arm : ℕ → Tree
| 0 => leaf
| k+1 => unary (unary (binary (arm k) (arm k)))
def nanostar (k : ℕ) : Tree := ternary (arm (k-1)) (arm (k-1)) (arm (k-1))
def treeGraph (t : Tree) : SimpleGraph (Fin (size t)) where
 Adj u v := u ≠ v ∧ ((u.val,v.val) ∈ edges t ∨ (v.val,u.val) ∈ edges t)
 symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
 loopless := ⟨fun _ h => h.1 rfl⟩
def orbit (A : Finset ℕ) : Set ℕ :=
 {m | ∃ a ∈ A, ∃ k : ℕ, (Nat.totient^[k]) a = m}
def phiGraph (A : Finset ℕ) : SimpleGraph (orbit A) where
 Adj u v := u ≠ v ∧ (Nat.totient u.val = v.val ∨ Nat.totient v.val = u.val)
 symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.symm⟩⟩
 loopless := ⟨fun _ h => h.1 rfl⟩
def Realizable (t : Tree) : Prop :=
 ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ Nonempty (treeGraph t ≃g phiGraph A)
def Conjecture349177 : Prop := ∀ k : ℕ, 4 ≤ k → ¬ Realizable (nanostar k)

theorem realizes_of_label {t : Tree} (lab : Fin (size t) → ℕ)
 (hinj : Function.Injective lab)
 (hpos : ∀ i, 0 < lab i)
 (hclosed : ∀ i, ∃ j, Nat.totient (lab i) = lab j)
 (hadj : ∀ i j, (treeGraph t).Adj i j ↔
    i ≠ j ∧ (Nat.totient (lab i) = lab j ∨ Nat.totient (lab j) = lab i)) :
 Realizable t := by
 let A : Finset ℕ := Finset.univ.image lab
 have hrange : ∀ m ∈ orbit A, ∃ i, lab i = m := by
  intro m hm
  obtain ⟨a,ha,k,hk⟩ := hm
  have ha' : ∃ i, lab i = a := by simpa [A] using ha
  have hk' : ∃ i, lab i = (Nat.totient^[k]) a := by
   clear hk
   induction k with
   | zero => simpa using ha'
   | succ k ih =>
     obtain ⟨i,hi⟩ := ih
     obtain ⟨j,hj⟩ := hclosed i
     exact ⟨j, by rw [Function.iterate_succ_apply', ← hi]; exact hj.symm⟩
  simpa [hk] using hk'
 let f : Fin (size t) → orbit A := fun i => ⟨lab i, lab i, by simp [A], 0, rfl⟩
 have hbij : Function.Bijective f := by
  constructor
  · intro i j h; exact hinj (congrArg Subtype.val h)
  · intro m; obtain ⟨i,hi⟩ := hrange m.val m.property
    exact ⟨i, Subtype.ext hi⟩
 let e := Equiv.ofBijective f hbij
 refine ⟨A, ?_, ⟨{ e with map_rel_iff' := ?_ }⟩⟩
 · intro a ha
   obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
   exact hpos i
 · intro i j
   change ((f i ≠ f j) ∧ (Nat.totient (lab i) = lab j ∨ Nat.totient (lab j) = lab i)) ↔ _
   rw [hadj]
   have hf : f i ≠ f j ↔ i ≠ j := by
    constructor
    · intro h h'; exact h (congrArg f h')
    · intro h h'; exact h (hbij.1 h')
   rw [hf]
end R162

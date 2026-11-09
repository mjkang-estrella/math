import Placement
set_option autoImplicit false
namespace Polyomino57.Diagonal
open Polyomino57

-- Eight Cartesian signed permutations: precisely the D4 action on square cells.
def d4 (swap nx ny : Bool) (p : GridPoint) : GridPoint :=
  (if nx then -(if swap then p.2 else p.1) else (if swap then p.2 else p.1),
   if ny then -(if swap then p.1 else p.2) else (if swap then p.1 else p.2))
def d4inv (swap nx ny : Bool) (p : GridPoint) : GridPoint :=
  if swap then (if ny then -p.2 else p.2,if nx then -p.1 else p.1)
  else (if nx then -p.1 else p.1,if ny then -p.2 else p.2)

theorem d4_inverse (swap nx ny : Bool) (p : GridPoint) :
    d4inv swap nx ny (d4 swap nx ny p) = p := by
  cases swap <;> cases nx <;> cases ny <;> simp [d4,d4inv]

theorem d4_witness (swap nx ny : Bool) (p : GridPoint) :
    d4 swap nx ny p ∈ witness ↔ p ∈ witness := by
  simp only [mem_witness]
  cases swap <;> cases nx <;> cases ny <;> dsimp [d4] <;> omega

theorem d4inv_witness (swap nx ny : Bool) (p : GridPoint) :
    d4inv swap nx ny p ∈ witness ↔ p ∈ witness := by
  simp only [mem_witness]
  cases swap <;> cases nx <;> cases ny <;> dsimp [d4inv] <;> omega

theorem d4_adj (swap nx ny : Bool) (p q : GridPoint) :
    Adj (d4 swap nx ny p) (d4 swap nx ny q) ↔ Adj p q := by
  cases swap <;> cases nx <;> cases ny <;> dsimp [d4,Adj] <;> omega

theorem d4_injective (swap nx ny : Bool) : Function.Injective (d4 swap nx ny) := by
  intro p q h
  have hh := congrArg (d4inv swap nx ny) h
  simpa only [d4_inverse] using hh

theorem d4_card (swap nx ny : Bool) (P : Finset GridPoint) :
    (P.image (d4 swap nx ny)).card = P.card :=
  Finset.card_image_of_injective _ (d4_injective swap nx ny)

theorem d4_connected (swap nx ny : Bool) {P : Finset GridPoint}
    (h : EdgeConnected P) : EdgeConnected (P.image (d4 swap nx ny)) := by
  refine ⟨h.1.image _,?_⟩
  intro p hp q hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
  apply Relation.ReflTransGen.lift (d4 swap nx ny) (fun x y hxy => ?_) a b (h.2 a ha b hb)
  exact ⟨Finset.mem_image.mpr ⟨x,hxy.1,rfl⟩,
    Finset.mem_image.mpr ⟨y,hxy.2.1,rfl⟩,(d4_adj swap nx ny x y).mpr hxy.2.2⟩

theorem d4inv_add (swap nx ny : Bool) (p q : GridPoint) :
    d4inv swap nx ny (p.1+q.1,p.2+q.2) =
    ((d4inv swap nx ny p).1+(d4inv swap nx ny q).1,
      (d4inv swap nx ny p).2+(d4inv swap nx ny q).2) := by
  cases swap <;> cases nx <;> cases ny <;> simp only [d4inv,Bool.false_eq_true, ↓reduceIte] <;> apply Prod.ext <;> dsimp <;> omega

-- Placement is a translation of the ORIGINAL P. No symmetry is allowed in the conclusion.
theorem recover_original_translation (swap nx ny : Bool) (P : Finset GridPoint)
    (d t : GridPoint) (h : translate t (translate d (P.image (d4 swap nx ny))) ⊆ witness) :
    ∃ z : GridPoint, translate z P ⊆ witness := by
  let z := d4inv swap nx ny (d.1+t.1,d.2+t.2)
  refine ⟨z,?_⟩
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have hm := h (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr
    ⟨_,Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩,rfl⟩)
  have hh := (d4inv_witness swap nx ny _).mpr hm
  have heq : (((d4 swap nx ny p).1+d.1)+t.1,((d4 swap nx ny p).2+d.2)+t.2) =
      ((d4 swap nx ny p).1+(d.1+t.1),(d4 swap nx ny p).2+(d.2+t.2)) := by
    ext <;> dsimp <;> omega
  rw [heq,d4inv_add swap nx ny (d4 swap nx ny p) (d.1+t.1,d.2+t.2),d4_inverse] at hh
  exact hh
end Polyomino57.Diagonal

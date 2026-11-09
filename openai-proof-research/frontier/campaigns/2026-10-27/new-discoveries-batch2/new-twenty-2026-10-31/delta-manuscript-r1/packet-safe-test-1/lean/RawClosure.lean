import Delta153
namespace RawClosure
open Delta153
inductive Pure : Graph → Graph → Prop
| refl (g) : Pure g g
| step {g h} (x : Nat) : x ∈ verts g → wye g x = true → Pure (reduce g x) h → Pure g h

def LocalClosed (g : Graph) (children : List Graph) : Bool :=
  (verts g).all fun x => !wye g x || children.contains (reduce g x)

theorem extend (g : Graph) (children : List Graph)
    (bound : 11 ≤ g.length) (check : LocalClosed g children = true)
    (childBound : ∀ k ∈ children, ∀ h, Pure k h → 11 ≤ h.length) :
    ∀ h, Pure g h → 11 ≤ h.length := by
  intro h path
  cases path with
  | refl => exact bound
  | step x hx hw tail =>
    have hc := List.all_eq_true.mp check x hx
    simp only [hw, Bool.not_true, Bool.false_or] at hc
    exact childBound _ (List.contains_iff_mem.mp hc) h tail

theorem closed_set_sound (S : Set Graph)
    (closed : ∀ g ∈ S, ∀ x ∈ verts g, wye g x = true → reduce g x ∈ S)
    (bound : ∀ g ∈ S, 11 ≤ g.length) {g h}
    (root : g ∈ S) (path : Pure g h) : 11 ≤ h.length := by
  have mem : h ∈ S := by
    induction path with
    | refl => exact root
    | @step g h x hx hw tail ih => exact ih (closed g root x hx hw)
  exact bound h mem

def IndexedClosed (g : Graph) (children : List (Nat × Graph)) : Bool :=
  (verts g).all fun x => !wye g x ||
    children.any (fun p => x == p.1 && reduce g x == p.2)

theorem indexed_extend (g : Graph) (children : List (Nat × Graph))
    (bound : 11 ≤ g.length) (check : IndexedClosed g children = true)
    (childBound : ∀ p ∈ children, ∀ h, Pure p.2 h → 11 ≤ h.length) :
    ∀ h, Pure g h → 11 ≤ h.length := by
  intro h path
  cases path with
  | refl => exact bound
  | step x hx hw tail =>
    have hc := List.all_eq_true.mp check x hx
    simp only [hw, Bool.not_true, Bool.false_or] at hc
    obtain ⟨p, hp, he⟩ := List.any_eq_true.mp hc
    have eq : reduce g x = p.2 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      exact he.2
    exact childBound p hp h (eq ▸ tail)
end RawClosure

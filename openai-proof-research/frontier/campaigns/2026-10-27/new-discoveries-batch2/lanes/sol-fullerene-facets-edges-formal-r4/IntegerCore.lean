import Mathlib.Data.Int.Basic
set_option autoImplicit false
set_option warningAsError true
namespace TripleCertificates
structure V where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq
def dp (a b : V) : ℤ := a.x*b.x+a.y*b.y+a.z*b.z
def det (a b c : V) : ℤ :=
  a.x*(b.y*c.z-b.z*c.y)-a.y*(b.x*c.z-b.z*c.x)+a.z*(b.x*c.y-b.y*c.x)
structure Point where
  num : V
  den : ℤ
  deriving DecidableEq
def active (a : V) (D : ℤ) (p : Point) : Prop := dp a p.num = D*p.den
instance (a : V) (D : ℤ) (p : Point) : Decidable (active a D p) := inferInstanceAs (Decidable (_ = _))
def same (p r : Point) : Prop :=
 p.num.x*r.den=r.num.x*p.den ∧ p.num.y*r.den=r.num.y*p.den ∧ p.num.z*r.den=r.num.z*p.den
instance (p r : Point) : Decidable (same p r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def core (a b c : V) (D : ℤ) (p : Point) : Prop :=
  0 < p.den ∧ det a b c ≠ 0 ∧ active a D p ∧ active b D p ∧ active c D p
instance (a b c : V) (D : ℤ) (p : Point) : Decidable (core a b c D p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
def bad (a b c t : V) (D : ℤ) (p : Point) : Prop := core a b c D p ∧ D*p.den < dp t p.num
instance (a b c t : V) (D : ℤ) (p : Point) : Decidable (bad a b c t D p) := inferInstanceAs (Decidable (_ ∧ _))
def good (a b c : V) (D : ℤ) (p r : Point) : Prop := core a b c D p ∧ 0 < r.den ∧ same p r
instance (a b c : V) (D : ℤ) (p r : Point) : Decidable (good a b c D p r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
structure Certificate where
 i : Fin 32
 j : Fin 32
 k : Fin 32
 point : Point
 isGood : Bool
 vertex : Fin 60
 violated : Fin 32
 deriving DecidableEq
def Certificate.ids (r : Certificate) := (r.i,r.j,r.k)
def checked (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point) (r : Certificate) : Prop :=
 if r.isGood then good (A r.i) (A r.j) (A r.k) D r.point (P r.vertex)
 else bad (A r.i) (A r.j) (A r.k) (A r.violated) D r.point
instance (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point) (r : Certificate) :
 Decidable (checked A D P r) := by unfold checked; infer_instance
theorem mergeChecked {A : Fin 32 → V} {D : ℤ} {P : Fin 60 → Point}
 {l r : List Certificate} (hl : ∀ c ∈ l, checked A D P c) (hr : ∀ c ∈ r, checked A D P c) :
 ∀ c ∈ l ++ r, checked A D P c := by
 intro c hc
 rcases List.mem_append.mp hc with hc | hc
 · exact hl c hc
 · exact hr c hc
end TripleCertificates

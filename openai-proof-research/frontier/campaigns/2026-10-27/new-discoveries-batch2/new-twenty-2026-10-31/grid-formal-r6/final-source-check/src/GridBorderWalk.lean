module
public import GridOrdinaryLayers
@[expose] public section
namespace Grid343536
open SimpleGraph Finset
set_option linter.unusedSimpArgs false

/-- Retain precisely the edges with both endpoints in a saturated set. -/
def restrictedGraph {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨by rintro u v ⟨h,hu,hv⟩; exact ⟨h.symm,hv,hu⟩⟩
  loopless := ⟨by intro u h; exact G.loopless.irrefl u h.1⟩

theorem restricted_equitable {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (hr : IsEquitable G r) (S : Set V)
    (hs : ∀ x y, r x y → (x ∈ S ↔ y ∈ S)) :
    IsEquitable (restrictedGraph G S) r := by
  classical
  intro u v huv w
  have eqcount (x : V) :
      Nat.card {a // (restrictedGraph G S).Adj x a ∧ r a w} =
        if x ∈ S ∧ w ∈ S then Nat.card {a // G.Adj x a ∧ r a w} else 0 := by
    by_cases h : x ∈ S ∧ w ∈ S
    · rw [ite_eq_left h]
      apply Nat.card_congr
      exact {
        toFun := fun a => ⟨a.val,a.property.1.1,a.property.2⟩
        invFun := fun a => ⟨a.val,⟨a.property.1,h.1,(hs _ _ a.property.2).mpr h.2⟩,a.property.2⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl }
    · rw [ite_eq_right h]
      let : IsEmpty {a // (restrictedGraph G S).Adj x a ∧ r a w} :=
        ⟨fun a => h ⟨a.property.1.2.1,(hs _ _ a.property.2).mp a.property.1.2.2⟩⟩
      simp
  rw [eqcount u,eqcount v]
  have he := hs u v huv
  simp only [he]
  split_ifs
  · exact hr u v huv w
  · rfl

/-- The saturated border has a neighbour-colour multiset rule. -/
theorem border_neighbor_rule {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r)
    {u v : Fin m × Fin n} (huv : r u v) :
    neighborCells (restrictedGraph (G m n) {x | gridLayer x = 1}) r u =
    neighborCells (restrictedGraph (G m n) {x | gridLayer x = 1}) r v := by
  apply (equitable_iff_neighborCells _ r).mp
    (restricted_equitable _ r hr _ (by
      intro x y h
      change gridLayer x = 1 ↔ gridLayer y = 1
      rw [grid_layer_invariant hm hn r hr x y h])) u v huv

/-- Cancellation at two degree-two neighbourhoods, retaining multiplicities of colours. -/
theorem two_neighbor_color {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (hr : IsEquitable G r) {u v a b c d : V}
    (huv : r u v) (hac : r a c) (hab : a ≠ b) (hcd : c ≠ d)
    (hu : ∀ z, G.Adj u z ↔ z = a ∨ z = b)
    (hv : ∀ z, G.Adj v z ↔ z = c ∨ z = d) : r b d := by
  classical
  have h := (equitable_iff_neighborCells G r).mp hr u v huv
  have he (x p q : V) (hne : p ≠ q) (hh : ∀ z, G.Adj x z ↔ z = p ∨ z = q) :
      neighborCells G r x = Quotient.mk r p ::ₘ Quotient.mk r q ::ₘ 0 := by
    have hf : univ.filter (G.Adj x) = {p,q} := by ext z; simp [hh z]
    simp [neighborCells,hf,Finset.insert_val_of_notMem, hne]
  rw [he u a b hab hu,he v c d hcd hv,Quotient.sound hac] at h
  exact Quotient.exact (by simpa using h)

/-- Explicit non-backtracking is required to identify two distinct side neighbours. -/
theorem nonbacktracking_color_walk {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (hr : IsEquitable G r) (x y : ℕ → V) (d : ℕ)
    (hzero : r (x 0) (y 0)) (hone : r (x 1) (y 1))
    (hx : ∀ t, 1 ≤ t → t < d → ∀ z, G.Adj (x t) z ↔ z = x (t-1) ∨ z = x (t+1))
    (hy : ∀ t, 1 ≤ t → t < d → ∀ z, G.Adj (y t) z ↔ z = y (t-1) ∨ z = y (t+1))
    (hnx : ∀ t, 1 ≤ t → t < d → x (t-1) ≠ x (t+1))
    (hny : ∀ t, 1 ≤ t → t < d → y (t-1) ≠ y (t+1)) :
    ∀ t, t ≤ d → r (x t) (y t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases h0 : t = 0
    · subst t; exact hzero
    by_cases h1 : t = 1
    · subst t; exact hone
    have hlow : 1 ≤ t-1 := by omega
    have hhigh : t-1 < d := by omega
    have he : t-1+1 = t := by omega
    rw [← he]
    exact two_neighbor_color G r hr (ih (t-1) (by omega) (by omega))
      (ih (t-1-1) (by omega) (by omega))
      (hnx (t-1) hlow hhigh) (hny (t-1) hlow hhigh)
      (hx (t-1) hlow hhigh) (hy (t-1) hlow hhigh)
/-- Matching side walks encounter their first colour-invariant marker simultaneously. -/
theorem color_walk_first_marker {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : Setoid V) (hr : IsEquitable G r) (x y : ℕ → V) (a b : ℕ)
    (P : V → Prop) (hp : ∀ u v, r u v → (P u ↔ P v))
    (hzero : r (x 0) (y 0)) (hone : r (x 1) (y 1))
    (hx : ∀ t, 1 ≤ t → t < min a b → ∀ z,
      G.Adj (x t) z ↔ z = x (t-1) ∨ z = x (t+1))
    (hy : ∀ t, 1 ≤ t → t < min a b → ∀ z,
      G.Adj (y t) z ↔ z = y (t-1) ∨ z = y (t+1))
    (hnx : ∀ t, 1 ≤ t → t < min a b → x (t-1) ≠ x (t+1))
    (hny : ∀ t, 1 ≤ t → t < min a b → y (t-1) ≠ y (t+1))
    (ha : P (x a)) (hb : P (y b))
    (hbeforex : ∀ t, t < a → ¬ P (x t))
    (hbeforey : ∀ t, t < b → ¬ P (y t)) : a = b := by
  have h := nonbacktracking_color_walk G r hr x y (min a b)
    hzero hone hx hy hnx hny (min a b) (Nat.le_refl _)
  have he := hp _ _ h
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab] at he
    by_contra hn
    exact hbeforey a (by omega) (he.mp ha)
  · rw [Nat.min_eq_right (by omega)] at he
    exact False.elim (hbeforex b (by omega) (he.mpr hb))
end Grid343536

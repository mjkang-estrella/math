module
public import GridDegrees
@[expose] public section
set_option linter.unusedSimpArgs false
namespace Grid343536

theorem row_degree_le {m n : ℕ} (hm : 2 ≤ m) (j : Fin n) :
    (G m n).degree (⟨0, by omega⟩, j) ≤ 3 := by
  rw [grid_degree_formula]
  simp only [Fin.val_mk, Nat.lt_irrefl, ↓reduceIte]
  split_ifs <;> omega

theorem side_next_unique {m n j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    (hjn : j + 1 < n) (x : Fin m × Fin n)
    (ha : (G m n).Adj (⟨0, by omega⟩, ⟨j, by omega⟩) x)
    (hd : (G m n).degree x ≤ 3)
    (hne : x ≠ (⟨0, by omega⟩, ⟨j-1, by omega⟩)) :
    x = (⟨0, by omega⟩, ⟨j+1, hjn⟩) := by
  have hi := x.1.isLt
  have hk := x.2.isLt
  rw [grid_degree_formula] at hd
  rcases (grid_adj_iff _ _).mp ha with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hv : x.1.val = 0 := congrArg Fin.val h1.symm
    have hv2 : x.2.val = j+1 := by
      have hn : ¬ (x.1.val = 0 ∧ x.2.val = j-1) := by
        rintro ⟨ha,hb⟩
        exact hne (Prod.ext (Fin.ext ha) (Fin.ext hb))
      change j + 1 = x.2.val ∨ x.2.val + 1 = j at h2
      omega
    exact Prod.ext (Fin.ext hv) (Fin.ext hv2)
  · have hv : x.1.val = 1 := by
      change 0+1 = x.1.val ∨ x.1.val+1 = 0 at h1
      omega
    have hv2 : x.2.val = j := congrArg Fin.val h2.symm
    simp only [hv,hv2] at hd
    simp only [show 0 < 1 by omega, show 1+1 < m by omega,
      hj, hjn, ↓reduceIte] at hd
    omega

/-- A graph isomorphism fixing an oriented initial corner flag follows that side
as far as both sides exist. Injectivity supplies explicit non-backtracking. -/
theorem side_prefix {m n p q : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (f : G m n ≃g G p q)
    (hzero : f (⟨0, by omega⟩, ⟨0, by omega⟩) = (⟨0, by omega⟩, ⟨0, by omega⟩))
    (hone : f (⟨0, by omega⟩, ⟨1, by omega⟩) = (⟨0, by omega⟩, ⟨1, by omega⟩)) :
    ∀ k (hkn : k < n) (hkq : k < q),
      f (⟨0, by omega⟩, ⟨k,hkn⟩) = (⟨0, by omega⟩, ⟨k,hkq⟩) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkn hkq
    by_cases h0 : k = 0
    · subst k; exact hzero
    by_cases h1 : k = 1
    · subst k; exact hone
    have h2 : 2 ≤ k := by omega
    suffices hs : f (⟨0,by omega⟩, ⟨k,hkn⟩) =
        (⟨0,by omega⟩, ⟨k-1+1,by omega⟩) by
      simpa only [show k-1+1=k by omega] using hs
    apply side_next_unique hp (j := k-1) (by omega) (by omega)
    · have ha : (G m n).Adj (⟨0,by omega⟩, ⟨k-1,by omega⟩)
          (⟨0,by omega⟩, ⟨k,hkn⟩) := by
        apply (grid_adj_iff _ _).mpr
        exact Or.inl ⟨rfl, Or.inl (by dsimp; omega)⟩
      have hh := f.map_rel_iff.mpr ha
      rw [ih (k-1) (by omega) (by omega) (by omega)] at hh
      exact hh
    · rw [f.degree_eq]
      exact row_degree_le (by omega) _
    · intro he
      have hh := ih (k-2) (by omega) (by omega) (by omega)
      have hv : f (⟨0,by omega⟩, ⟨k,hkn⟩) =
          f (⟨0,by omega⟩, ⟨k-2,by omega⟩) := by
        rw [hh, he]
        congr 2
      have hv2 := congrArg (fun x : Fin m × Fin n => x.2.val) (f.injective hv)
      dsimp at hv2
      omega

/-- The first terminal corner is reached simultaneously on both sides. -/
theorem side_length_eq {m n p q : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (f : G m n ≃g G p q)
    (hzero : f (⟨0, by omega⟩, ⟨0, by omega⟩) = (⟨0, by omega⟩, ⟨0, by omega⟩))
    (hone : f (⟨0, by omega⟩, ⟨1, by omega⟩) = (⟨0, by omega⟩, ⟨1, by omega⟩)) : n = q := by
  have key : ∀ {a b c d : ℕ} (_ha : 3 ≤ a) (_hb : 3 ≤ b) (_hc : 3 ≤ c) (_hd : 3 ≤ d),
      ∀ (f : G a b ≃g G c d),
      f (⟨0,by omega⟩, ⟨0,by omega⟩) = (⟨0,by omega⟩, ⟨0,by omega⟩) →
      f (⟨0,by omega⟩, ⟨1,by omega⟩) = (⟨0,by omega⟩, ⟨1,by omega⟩) → b ≤ d := by
    intro a b c d ha hb hc hd g h0 h1
    by_contra h
    have hdb : d < b := by omega
    have he := side_prefix ha hb hc hd g h0 h1 (d-1) (by omega) (by omega)
    have hh := g.degree_eq (⟨0,by omega⟩, ⟨d-1,by omega⟩)
    rw [he, grid_degree_formula, grid_degree_formula] at hh
    simp only [Fin.val_mk, show 0 < d-1 by omega, show ¬ d-1+1 < d by omega,
      show d-1+1 < b by omega, show 0+1 < a by omega, show 0+1 < c by omega,
      Nat.lt_irrefl, ↓reduceIte] at hh
    omega
  apply Nat.le_antisymm (key hm hn hp hq f hzero hone)
  apply key hp hq hm hn f.symm
  · exact f.symm_apply_eq.mpr hzero.symm
  · exact f.symm_apply_eq.mpr hone.symm

/-- An oriented corner flag is a determining set for the full automorphism group. -/
theorem fixed_flag_identity {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (g : G m n ≃g G m n)
    (hzero : g (⟨0, by omega⟩, ⟨0, by omega⟩) = (⟨0, by omega⟩, ⟨0, by omega⟩))
    (hone : g (⟨0, by omega⟩, ⟨1, by omega⟩) = (⟨0, by omega⟩, ⟨1, by omega⟩)) : g = 1 := by
  have he := row_determinism (Setoid.ker (id : Fin m × Fin n → _))
    (by intro u v h w; change u = v at h; subst v; rfl) g
    (by intro j h0; exact side_prefix hm hn hm hn g hzero hone j.val j.isLt j.isLt)
  apply DFunLike.ext
  exact he
end Grid343536

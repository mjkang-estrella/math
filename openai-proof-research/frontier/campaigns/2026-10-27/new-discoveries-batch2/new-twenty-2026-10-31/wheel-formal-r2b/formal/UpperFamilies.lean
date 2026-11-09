import UpperCycle
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace WheelFormal

noncomputable def profileFamily (t : ℕ) (h : Prop)
    (A B : ZMod (2*t+1) → Prop) (R : ZMod (2*t+1) → ZMod (2*t+1) → Prop) :
    WheelSet t := by
  classical
  exact Finset.univ.filter fun v => match v with
    | (none,none) => h
    | (some i,none) => A i
    | (none,some j) => B j
    | (some i,some j) => R i j

theorem profileFamily_independent (t : ℕ) (h : Prop)
    (A B : ZMod (2*t+1) → Prop) (R : ZMod (2*t+1) → ZMod (2*t+1) → Prop)
    (ha : ∀ x y, A x → A y → ¬ rimAdj (2*t+1) x y)
    (hb : ∀ x y, B x → B y → ¬ rimAdj (2*t+1) x y)
    (hhA : h → ∀ x, ¬ A x) (hhB : h → ∀ x, ¬ B x)
    (hrA : ∀ i j, R i j → ¬ A i) (hrB : ∀ i j, R i j → ¬ B j)
    (hrX : ∀ i k j, R i j → R k j → ¬ rimAdj (2*t+1) i k)
    (hrY : ∀ i j k, R i j → R i k → ¬ rimAdj (2*t+1) j k) :
    Independent (wheelSquare t) (profileFamily t h A B R) := by
  classical
  rintro ⟨u,v⟩ huv ⟨x,y⟩ hxy _ he
  cases u <;> cases v <;> cases x <;> cases y <;>
    simp only [profileFamily, Finset.mem_filter, Finset.mem_univ, true_and] at huv hxy <;>
    simp only [wheelSquare, SimpleGraph.boxProd, wheel, Option.some.injEq,
      reduceCtorEq, and_false, false_and, or_false, false_or] at he
  all_goals first
    | contradiction
    | exact hhA huv _ hxy
    | exact hhB huv _ hxy
    | exact hhA hxy _ huv
    | exact hhB hxy _ huv
    | exact ha _ _ huv hxy he.1
    | exact hb _ _ huv hxy he.1
    | (rcases he with ⟨_,rfl⟩; exact hrA _ _ hxy huv)
    | (rcases he with ⟨_,rfl⟩; exact hrB _ _ hxy huv)
    | (rcases he with ⟨_,rfl⟩; exact hrA _ _ huv hxy)
    | (rcases he with ⟨_,rfl⟩; exact hrB _ _ huv hxy)
    | (rcases he with ⟨he,rfl⟩ | ⟨he,hij⟩
       · exact hrX _ _ _ huv hxy he
       · cases hij; exact hrY _ _ _ huv hxy he)

noncomputable def family0 (t : ℕ) (s : ZMod (2*t+1)) : WheelSet t :=
  profileFamily t True (fun _ => False) (fun _ => False)
    (fun i j => alternating t (i-j-s))

noncomputable def family1 (t : ℕ) (a b : ZMod (2*t+1)) (c : Fin 2) : WheelSet t :=
  profileFamily t False (fun i => i = a) (fun j => j = b)
    (fun i j => i ≠ a ∧ j ≠ b ∧ ((i-a-1).val+(j-b-1).val)%2 = c.val)

/-- The two path endpoints are distinguished by the last representative.
All other nondeleted coordinates have odd representatives. -/
def roleRim (t : ℕ) (a b i j : ZMod (2*t+1)) : Prop :=
  ¬ alternating t (i-a) ∧ ¬ alternating t (j-b) ∧
    ((i-a).val = 2*t ↔ (j-b).val = 2*t)

noncomputable def family2 (t : ℕ) (a b : ZMod (2*t+1)) : WheelSet t :=
  profileFamily t False (fun i => alternating t (i-a))
    (fun j => alternating t (j-b)) (roleRim t a b)

theorem family0_independent (t : ℕ) (s : ZMod (2*t+1)) :
    Independent (wheelSquare t) (family0 t s) := by
  apply profileFamily_independent
  all_goals try tauto
  · intro i k j hi hk he
    apply alternating_independent t _ _ hi hk
    exact (rimAdj_translate t (j+s) i k).mpr he |>.imp (by simp [sub_add_eq_sub_sub]) (by simp [sub_add_eq_sub_sub])
  · intro i j k hj hk he
    apply alternating_independent t _ _ hj hk
    rcases he with ⟨hn,he | he⟩
    · constructor
      · intro h; apply hn; linear_combination -h
      · right; linear_combination he
    · constructor
      · intro h; apply hn; linear_combination -h
      · left; linear_combination he

theorem family1_independent (t : ℕ) (a b : ZMod (2*t+1)) (c : Fin 2) :
    Independent (wheelSquare t) (family1 t a b c) := by
  apply profileFamily_independent
  · intro x y hx hy; subst x; subst y; simp [rimAdj]
  · intro x y hx hy; subst x; subst y; simp [rimAdj]
  · tauto
  · tauto
  · intro i j h; exact h.1
  · intro i j h; exact h.2.1
  · intro i k j hi hk he
    have hp := deleted_parity t a i k hi.1 hk.1 he
    have hc := hi.2.2.trans hk.2.2.symm
    omega
  · intro i j k hj hk he
    have hp := deleted_parity t b j k hj.2.1 hk.2.1 he
    have hc := hj.2.2.trans hk.2.2.symm
    omega

theorem nondeleted_edge (t : ℕ) (x y : ZMod (2*t+1))
    (hx : ¬ alternating t x) (hy : ¬ alternating t y)
    (he : rimAdj (2*t+1) x y) :
    ¬ (x.val = 2*t ↔ y.val = 2*t) := by
  have hv := rimAdj_val t x y he
  have hxx := ZMod.val_lt x
  have hyy := ZMod.val_lt y
  unfold alternating at hx hy
  intro hh
  have hl : x.val = 2*t ∨ y.val = 2*t := by omega
  rcases hl with hl | hl
  · exact he.1 (ZMod.val_injective _ (hl.trans (hh.mp hl).symm))
  · exact he.1 (ZMod.val_injective _ ((hh.mpr hl).trans hl.symm))

theorem family2_independent (t : ℕ) (a b : ZMod (2*t+1)) :
    Independent (wheelSquare t) (family2 t a b) := by
  apply profileFamily_independent
  · intro x y hx hy he
    exact alternating_independent t _ _ hx hy ((rimAdj_translate t a x y).mpr he)
  · intro x y hx hy he
    exact alternating_independent t _ _ hx hy ((rimAdj_translate t b x y).mpr he)
  · tauto
  · tauto
  · intro i j h; exact h.1
  · intro i j h; exact h.2.1
  · intro i k j hi hk he
    exact nondeleted_edge t _ _ hi.1 hk.1 ((rimAdj_translate t a i k).mpr he)
      (hi.2.2.trans hk.2.2.symm)
  · intro i j k hj hk he
    exact nondeleted_edge t _ _ hj.2.1 hk.2.1 ((rimAdj_translate t b j k).mpr he)
      (hj.2.2.symm.trans hk.2.2)
end WheelFormal

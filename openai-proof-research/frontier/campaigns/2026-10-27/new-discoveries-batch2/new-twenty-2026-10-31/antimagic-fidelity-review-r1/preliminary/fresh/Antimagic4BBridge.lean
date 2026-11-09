import Antimagic2Structure

namespace Antimagic.Round4B

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph W} [DecidableRel H.Adj] {t n : ℕ}

abbrev Layer (S : FullTree G t n) (h : ℕ) := {v : V // S.depth v = h}

noncomputable def slots (S : FullTree G t n) (v : V) (hv : S.depth v < n) :
    {w : V // S.child v w} ≃ Fin t := by
  classical
  have hc : Fintype.card {w : V // S.child v w} = t := by
    let := S.childDec v
    rw [Fintype.card_subtype, S.child_count, ite_eq_left hv]
  exact (Fintype.equivFin _).trans (finCongr hc)

/-- Projection from a parent layer and one of its children to the next layer. -/
def descend (S : FullTree G t n) (h : ℕ)
    (a : (u : Layer S h) × {v : V // S.child u.val v}) : Layer S (h + 1) :=
  ⟨a.2.val, by rw [S.child_depth _ _ a.2.property, a.1.property]⟩

theorem descend_bijective (S : FullTree G t n) (h : ℕ) :
    Function.Bijective (descend S h) := by
  constructor
  · intro a b hab
    have hv : a.2.val = b.2.val := congrArg Subtype.val hab
    have hn : a.2.val ≠ S.root := by
      intro he
      have hz := (S.root_zero _).mpr he
      have hd := S.child_depth _ _ a.2.property
      omega
    obtain ⟨p, _, hp⟩ := S.unique_parent _ hn
    have hu : a.1 = b.1 := by
      apply Subtype.ext
      exact (hp _ a.2.property).trans (hp _ (hv.symm ▸ b.2.property)).symm
    cases a with | mk a ac =>
      cases b with | mk b bc =>
        dsimp at hu
        subst b
        have : ac = bc := Subtype.ext hv
        subst bc
        rfl
  · intro v
    have hn : v.val ≠ S.root := by
      intro he
      have hz := (S.root_zero _).mpr he
      have := v.property
      omega
    obtain ⟨p, hp, _⟩ := S.unique_parent _ hn
    have hd : S.depth p = h := by
      have := S.child_depth _ _ hp
      have := v.property
      omega
    exact ⟨⟨⟨p, hd⟩, ⟨v.val, hp⟩⟩, rfl⟩

noncomputable def step (S : FullTree G t n) (h : ℕ) (hh : h < n) :
    Layer S (h + 1) ≃ Layer S h × Fin t :=
  (Equiv.ofBijective (descend S h) (descend_bijective S h)).symm |>.trans
    ((Equiv.sigmaCongrRight (fun (u : Layer S h) => slots S u.val (by rw [u.property]; exact hh))).trans
      (Equiv.sigmaEquivProd _ _))

theorem step_parent (S : FullTree G t n) (h : ℕ) (hh : h < n)
    (v : Layer S (h + 1)) : S.child ((step S h hh v).1.val) v.val := by
  classical
  let e := Equiv.ofBijective (descend S h) (descend_bijective S h)
  have he := congrArg Subtype.val (e.apply_symm_apply v)
  exact he ▸ (e.symm v).2.property

theorem step_parent_iff (S : FullTree G t n) (h : ℕ) (hh : h < n)
    (u : Layer S h) (v : Layer S (h + 1)) :
    S.child u.val v.val ↔ (step S h hh v).1 = u := by
  constructor
  · intro hc
    have hn : v.val ≠ S.root := by
      intro he
      have := (S.root_zero _).mpr he
      have := v.property
      omega
    obtain ⟨p, _, hp⟩ := S.unique_parent _ hn
    apply Subtype.ext
    exact (hp _ (step_parent S h hh v)).trans (hp _ hc).symm
  · intro he
    simpa only [he] using step_parent S h hh v

noncomputable def zeroEquiv (S : FullTree G t n) (T : FullTree H t n) :
    Layer S 0 ≃ Layer T 0 where
  toFun _ := ⟨T.root, (T.root_zero _).mpr rfl⟩
  invFun _ := ⟨S.root, (S.root_zero _).mpr rfl⟩
  left_inv v := Subtype.ext ((S.root_zero _).mp v.property).symm
  right_inv v := Subtype.ext ((T.root_zero _).mp v.property).symm

noncomputable def layers (S : FullTree G t n) (T : FullTree H t n) :
    (h : ℕ) → h ≤ n → Layer S h ≃ Layer T h
  | 0, _ => zeroEquiv S T
  | h + 1, hh => (step S h (by omega)).trans
      ((Equiv.prodCongr (layers S T h (by omega)) (Equiv.refl (Fin t))).trans
        (step T h (by omega)).symm)

 theorem layers_parent (S : FullTree G t n) (T : FullTree H t n)
    (h : ℕ) (hh : h + 1 ≤ n) (v : Layer S (h + 1)) :
    (step T h (by omega) (layers S T (h + 1) hh v)).1 =
      layers S T h (by omega) (step S h (by omega) v).1 := by
  simp [layers]

noncomputable def vertexMap (S : FullTree G t n) (T : FullTree H t n) (v : V) : W :=
  (layers S T (S.depth v) (S.depth_le v) ⟨v, rfl⟩).val

theorem vertexMap_depth (S : FullTree G t n) (T : FullTree H t n) (v : V) :
    T.depth (vertexMap S T v) = S.depth v :=
  (layers S T _ _ ⟨v, rfl⟩).property

theorem vertexMap_layer (S : FullTree G t n) (T : FullTree H t n)
    (h : ℕ) (hh : h ≤ n) (v : Layer S h) :
    vertexMap S T v.val = (layers S T h hh v).val := by
  rcases v with ⟨v, hv⟩
  subst h
  rfl

theorem vertexMap_bijective (S : FullTree G t n) (T : FullTree H t n) :
    Function.Bijective (vertexMap S T) := by
  constructor
  · intro u v huv
    have hd : S.depth u = S.depth v := by
      simpa only [vertexMap_depth] using congrArg T.depth huv
    have he : layers S T (S.depth v) (S.depth_le v) ⟨u, hd⟩ =
        layers S T (S.depth v) (S.depth_le v) ⟨v, rfl⟩ := by
      apply Subtype.ext
      simpa only [← vertexMap_layer] using huv
    exact congrArg Subtype.val ((layers S T _ _).injective he)
  · intro w
    let v := (layers S T (T.depth w) (T.depth_le w)).symm ⟨w, rfl⟩
    refine ⟨v.val, ?_⟩
    rw [vertexMap_layer S T _ (T.depth_le w) v]
    exact congrArg Subtype.val ((layers S T _ _).apply_symm_apply ⟨w, rfl⟩)

theorem vertexMap_child (S : FullTree G t n) (T : FullTree H t n) (u v : V) :
    S.child u v ↔ T.child (vertexMap S T u) (vertexMap S T v) := by
  have aux (h : ℕ) (hh : h + 1 ≤ n) (u : Layer S h) (v : Layer S (h + 1)) :
      S.child u.val v.val ↔ T.child (vertexMap S T u.val) (vertexMap S T v.val) := by
    rw [vertexMap_layer S T h (by omega) u, vertexMap_layer S T (h + 1) hh v,
      step_parent_iff S h (by omega), step_parent_iff T h (by omega), layers_parent]
    exact ((layers S T h (by omega)).injective.eq_iff).symm
  constructor
  · intro hc
    have hd := S.child_depth _ _ hc
    exact (aux (S.depth u) (by have := S.depth_le v; omega) ⟨u, rfl⟩ ⟨v, hd⟩).mp hc
  · intro hc
    have hd : S.depth v = S.depth u + 1 := by
      simpa only [vertexMap_depth] using T.child_depth _ _ hc
    exact (aux (S.depth u) (by have := S.depth_le v; omega) ⟨u, rfl⟩ ⟨v, hd⟩).mpr hc

noncomputable def fullTreeIso (S : FullTree G t n) (T : FullTree H t n) : G ≃g H where
  toEquiv := Equiv.ofBijective (vertexMap S T) (vertexMap_bijective S T)
  map_rel_iff' := by
    intro u v
    change H.Adj (vertexMap S T u) (vertexMap S T v) ↔ G.Adj u v
    rw [T.adj_iff, S.adj_iff, ← vertexMap_child, ← vertexMap_child]

#print axioms fullTreeIso
end Antimagic.Round4B

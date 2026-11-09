import Sigma.PathExtension

namespace Sigma365710

/-- Four distinct vertices whose induced graph is a path, in path order. -/
def InducedP4 {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
  ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d

/-- Literal complementary independent parts with all cross edges. -/
def HasCompleteBipartition {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, ∀ u v, G.Adj u v ↔ (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)

theorem two_step_twins {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (hp : ¬ ∃ a b c d, InducedP4 G a b c d)
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) :
    ∀ x, G.Adj u x ↔ G.Adj w x := by
  classical
  have one : ∀ {u v w x : V}, G.Adj u v → G.Adj v w → G.Adj u x → G.Adj w x := by
    intro u v w x huv hvw hux
    by_contra hwx
    have huw : ¬ G.Adj u w := fun h => no_triangle G hG huv h hvw
    have hvx : ¬ G.Adj v x := fun h => no_triangle G hG huv hux h
    have huwne : u ≠ w := by intro e; subst w; exact hwx hux
    have hvxne : v ≠ x := by intro e; subst x; exact hwx hvw.symm
    apply hp
    exact ⟨x, u, v, w, hux.ne.symm, hvxne.symm, fun e => huw (e ▸ hux),
      huv.ne, huwne, hvw.ne, hux.symm, huv, hvw,
      fun h => hvx h.symm, fun h => hwx h.symm, huw⟩
  intro x
  exact ⟨one huv hvw, one hvw.symm huv.symm⟩

theorem completeBipartition_or_inducedP4 {V : Type*} (G : SimpleGraph V)
    (hc : G.Connected) (ht : G.CliqueFree 3) :
    HasCompleteBipartition G ∨ ∃ a b c d, InducedP4 G a b c d := by
  classical
  by_cases hp : ∃ a b c d, InducedP4 G a b c d
  · exact Or.inr hp
  left
  obtain ⟨v⟩ := hc.nonempty
  have classify : ∀ x, G.Adj v x ∨ ∀ z, G.Adj v z ↔ G.Adj x z := by
    intro x
    obtain ⟨p⟩ := hc.preconnected v x
    have walkprop : ∀ {y x : V}, G.Walk y x →
        (G.Adj v y ∨ ∀ z, G.Adj v z ↔ G.Adj y z) →
        (G.Adj v x ∨ ∀ z, G.Adj v z ↔ G.Adj x z) := by
      intro y x p
      induction p with
      | nil => exact id
      | @cons y z x hyz p ih =>
        intro h
        apply ih
        rcases h with h | h
        · exact Or.inr (two_step_twins G ht hp h hyz)
        · exact Or.inl ((h z).mpr hyz)
    exact walkprop p (Or.inr (fun _ => Iff.rfl))
  refine ⟨{x | G.Adj v x}, ?_⟩
  intro x y
  change G.Adj x y ↔ (G.Adj v x ∧ ¬ G.Adj v y) ∨ (¬ G.Adj v x ∧ G.Adj v y)
  have twins : ∀ x, ¬ G.Adj v x → ∀ z, G.Adj v z ↔ G.Adj x z := by
    intro x hx
    exact (classify x).resolve_left hx
  constructor
  · intro hxy
    by_cases hx : G.Adj v x
    · exact Or.inl ⟨hx, fun hy => no_triangle G ht hx hy hxy⟩
    · exact Or.inr ⟨hx, (twins x hx y).mpr hxy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact ((twins y hy x).mp hx).symm
    · exact (twins x hx y).mp hy

theorem inducedP4_of_not_completeBipartition {V : Type*} (G : SimpleGraph V)
    (hc : G.Connected) (ht : G.CliqueFree 3) (hb : ¬ HasCompleteBipartition G) :
    ∃ a b c d, InducedP4 G a b c d :=
  (completeBipartition_or_inducedP4 G hc ht).resolve_left hb

end Sigma365710

# Lean source appendix

Modules are listed in import order.

## RobustCover.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

namespace RobustCover

variable {V : Type}

structure OneSelection (G : SimpleGraph V) where
  pick : V → Option (Sym2 V)
  incident : ∀ v e, pick v = some e → e ∈ G.edgeSet ∧ v ∈ e

def OneSelection.removed {G : SimpleGraph V} (s : OneSelection G) : SimpleGraph V :=
  G.deleteEdges {e | ∃ v, s.pick v = some e}

def emptySelection (G : SimpleGraph V) : OneSelection G :=
  ⟨fun _ => none, by simp⟩

theorem empty_removed (G : SimpleGraph V) : (emptySelection G).removed = G := by
  simp [OneSelection.removed, emptySelection]

def HasCliqueCover (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ u v, u ≠ v → c u = c v → G.Adj u v

noncomputable def theta (G : SimpleGraph V) : ℕ := sInf {k | HasCliqueCover G k}

noncomputable def theta1 (G : SimpleGraph V) : ℕ :=
  sSup (Set.range fun s : OneSelection G => theta s.removed)

theorem theta_le {G : SimpleGraph V} {k : ℕ} (h : HasCliqueCover G k) : theta G ≤ k :=
  csInf_le' (s := {j | HasCliqueCover G j}) h

theorem singleton_cover [Fintype V] (G : SimpleGraph V) :
    HasCliqueCover G (Fintype.card V) := by
  let e := Fintype.equivFin V
  exact ⟨e, fun _ _ hn he => (hn (e.injective he)).elim⟩

theorem cover_theta [Fintype V] (G : SimpleGraph V) : HasCliqueCover G (theta G) :=
  csInf_mem (s := {j | HasCliqueCover G j}) ⟨_, singleton_cover G⟩

theorem theta_mono [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    theta H ≤ theta G := by
  obtain ⟨c, hc⟩ := cover_theta G
  exact theta_le ⟨c, fun u v hn he => h (hc u v hn he)⟩

theorem deletion_le_theta1 [Fintype V] {G : SimpleGraph V} (s : OneSelection G) :
    theta s.removed ≤ theta1 G := by
  unfold theta1
  apply le_csSup (s := Set.range fun r : OneSelection G => theta r.removed) _ ⟨s, rfl⟩
  exact ⟨Fintype.card V, by rintro _ ⟨r, rfl⟩; exact theta_le (singleton_cover r.removed)⟩

theorem theta_le_theta1 [Fintype V] (G : SimpleGraph V) : theta G ≤ theta1 G := by
  simpa only [empty_removed] using deletion_le_theta1 (emptySelection G)

theorem theta1_attained [Fintype V] (G : SimpleGraph V) :
    ∃ s : OneSelection G, theta s.removed = theta1 G := by
  have hm : theta1 G ∈ Set.range (fun s : OneSelection G => theta s.removed) := by
    apply Nat.sSup_mem
    · exact ⟨_, ⟨emptySelection G, rfl⟩⟩
    · exact ⟨Fintype.card V, by rintro _ ⟨s, rfl⟩; exact theta_le (singleton_cover s.removed)⟩
  exact hm


def SelectsAtNonisolates {G : SimpleGraph V} (s : OneSelection G) : Prop :=
  ∀ v, (∃ w, G.Adj v w) → ∃ e, s.pick v = some e

noncomputable def completeSelection {G : SimpleGraph V} (s : OneSelection G) :
    OneSelection G := by
  classical
  refine ⟨fun v => (s.pick v).orElse fun _ =>
    if h : ∃ w, G.Adj v w then some s(v, Classical.choose h) else none, ?_⟩
  intro v e he
  cases hp : s.pick v with
  | some a =>
    exact s.incident v e (by simpa [hp] using he)
  | none =>
    simp only [hp, Option.orElse] at he
    split at he
    · have heq := Option.some.inj he
      subst e
      simpa using Classical.choose_spec ‹∃ w, G.Adj v w›
    · cases he

theorem complete_selects {G : SimpleGraph V} (s : OneSelection G) :
    SelectsAtNonisolates (completeSelection s) := by
  classical
  intro v hv
  unfold completeSelection
  cases hp : s.pick v <;> simp [hp, hv, Option.orElse]

theorem complete_removed_le {G : SimpleGraph V} (s : OneSelection G) :
    (completeSelection s).removed ≤ s.removed := by
  apply SimpleGraph.deleteEdges_anti
  rintro e ⟨v, hv⟩
  exact ⟨v, by simp [completeSelection, hv, Option.orElse]⟩

noncomputable def theta1Required (G : SimpleGraph V) : ℕ :=
  sSup (Set.range fun s : {s : OneSelection G // SelectsAtNonisolates s} => theta s.val.removed)

theorem theta1Required_eq [Fintype V] (G : SimpleGraph V) : theta1Required G = theta1 G := by
  obtain ⟨s, hs⟩ := theta1_attained G
  let r : {s : OneSelection G // SelectsAtNonisolates s} :=
    ⟨completeSelection s, complete_selects s⟩
  unfold theta1Required
  refine le_antisymm (csSup_le ⟨_, ⟨r, rfl⟩⟩ ?_) ?_
  · rintro _ ⟨t, rfl⟩
    exact deletion_le_theta1 t.val
  · rw [← hs]
    apply (theta_mono (complete_removed_le s)).trans
    apply le_csSup (s := Set.range fun t : {t : OneSelection G // SelectsAtNonisolates t} =>
      theta t.val.removed) _ ⟨r, rfl⟩
    exact ⟨Fintype.card V, by rintro _ ⟨t, rfl⟩; exact theta_le (singleton_cover t.val.removed)⟩

noncomputable def orderedSelection (G : SimpleGraph V) (x y : V) : OneSelection G := by
  classical
  refine ⟨fun z => if G.Adj z x then some s(z, x)
    else if z ≠ x ∧ G.Adj z y then some s(z, y) else none, ?_⟩
  intro v e he
  split at he
  · have h := Option.some.inj he
    subst e
    simpa using ‹G.Adj v x›
  · split at he
    · have h := Option.some.inj he
      subst e
      simpa using (‹v ≠ x ∧ G.Adj v y›).2
    · cases he

theorem ordered_isolates (G : SimpleGraph V) (x y z : V) :
    ¬ (orderedSelection G x y).removed.Adj z x := by
  classical
  rw [OneSelection.removed, SimpleGraph.deleteEdges_adj]
  rintro ⟨hz, hnot⟩
  exact hnot ⟨z, by simp [orderedSelection, hz]⟩

theorem ordered_retains_compatible (G : SimpleGraph V) {x y z : V}
    (hz : z ≠ x) (hyz : (orderedSelection G x y).removed.Adj z y) : G.Adj z x := by
  classical
  rw [OneSelection.removed, SimpleGraph.deleteEdges_adj] at hyz
  by_contra hn
  exact hyz.2 ⟨z, by simp [orderedSelection, hn, hz, hyz.1]⟩

theorem exists_selection_increase [Fintype V] (G : SimpleGraph V) {x y : V}
    (h : G.Adj x y) : ∃ s : OneSelection G, theta G + 1 ≤ theta s.removed := by
  classical
  let s := orderedSelection G x y
  refine ⟨s, ?_⟩
  let k := theta s.removed
  obtain ⟨c, hc⟩ := cover_theta s.removed
  have singleton : ∀ z, c z = c x → z = x := by
    intro z hz
    by_contra hn
    exact ordered_isolates G x y z (hc z x hn hz)
  have hy : c y ≠ c x := fun he => h.ne (singleton y he).symm
  let d : V → Fin k := fun z => if z = x then c y else c z
  have hd : ∀ z, d z ≠ c x := by
    intro z
    by_cases hz : z = x
    · simpa [d, hz] using hy
    · simpa [d, hz] using mt (singleton z) hz
  have compatibility : ∀ z, c z = c y → G.Adj z x := by
    intro z he
    by_cases hz : z = y
    · subst z
      exact h.symm
    have hzx : z ≠ x := by
      rintro rfl
      exact hy he.symm
    exact ordered_retains_compatible G hzx (hc z y hz he)
  have merged : ∀ u v, u ≠ v → d u = d v → G.Adj u v := by
    intro u v hn he
    by_cases hu : u = x
    · subst u
      exact (compatibility v (by simpa [d, Ne.symm hn] using he.symm)).symm
    by_cases hv : v = x
    · subst v
      exact compatibility u (by simpa [d, hn] using he)
    exact SimpleGraph.deleteEdges_le (G := G) _ (hc u v hn (by simpa [d, hu, hv] using he))
  let A := {i : Fin k // i ≠ c x}
  have hcard : Fintype.card A = k - 1 := by
    classical
    change Fintype.card {i : Fin k // ¬ i = c x} = k - 1
    rw [Fintype.card_subtype_compl]
    simp
  let e : A ≃ Fin (k - 1) := Fintype.equivFinOfCardEq hcard
  have hle : theta G ≤ k - 1 := theta_le
    ⟨fun z => e ⟨d z, hd z⟩,
      fun u v hn he => merged u v hn (congrArg Subtype.val (e.injective he))⟩
  have hk := (c x).isLt
  change theta G + 1 ≤ k
  omega

theorem robust_theta_strict [Fintype V] (G : SimpleGraph V) :
    theta1 G = theta G ↔ G = ⊥ := by
  constructor
  · intro he
    apply le_antisymm _ bot_le
    intro x y h
    obtain ⟨s, hs⟩ := exists_selection_increase G h
    have := hs.trans (deletion_le_theta1 s)
    omega
  · rintro rfl
    refine le_antisymm (csSup_le ⟨_, ⟨emptySelection ⊥, rfl⟩⟩ ?_) (theta_le_theta1 ⊥)
    rintro _ ⟨s, rfl⟩
    have hr : s.removed = ⊥ := le_antisymm (SimpleGraph.deleteEdges_le (G := ⊥) _) bot_le
    change theta s.removed ≤ theta (⊥ : SimpleGraph V)
    rw [hr]

theorem robust_theta_required_strict [Fintype V] (G : SimpleGraph V) :
    theta1Required G = theta G ↔ G = ⊥ := by
  rw [theta1Required_eq]
  exact robust_theta_strict G

def Conjecture1 : Prop :=
  ∀ {W : Type} [Fintype W] (G : SimpleGraph W), G ≠ ⊥ → theta G < theta1 G

theorem conjecture1 : Conjecture1 := by
  intro W _ G h
  exact lt_of_le_of_ne (theta_le_theta1 G) (Ne.symm (mt (robust_theta_strict G).mp h))

theorem mathdb_358270 [Fintype V] (G : SimpleGraph V)
    (_hiso : ∀ v, ∃ w, G.Adj v w) : theta1 G = theta G ↔ G = ⊥ :=
  robust_theta_strict G

end RobustCover

#check RobustCover.theta1_attained
#check RobustCover.theta1Required_eq
#check RobustCover.robust_theta_required_strict
#check RobustCover.exists_selection_increase
#check RobustCover.robust_theta_strict
#check RobustCover.Conjecture1
#check RobustCover.conjecture1
#check RobustCover.mathdb_358270
#print axioms RobustCover.theta1_attained
#print axioms RobustCover.theta1Required_eq
#print axioms RobustCover.robust_theta_required_strict
#print axioms RobustCover.exists_selection_increase
#print axioms RobustCover.robust_theta_strict
#print axioms RobustCover.conjecture1
#print axioms RobustCover.mathdb_358270
```


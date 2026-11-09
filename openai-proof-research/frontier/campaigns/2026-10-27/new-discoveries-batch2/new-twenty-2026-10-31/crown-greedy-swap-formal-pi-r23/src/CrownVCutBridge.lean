import CrownVClass2

/-!
Cut-vertex neighbor bridge (r9 milestone): rerouting of `insert t D`-paths.

`sameC_of_clique`: if every two `D`-neighbors of `t` are `D`-connected, then
every `insert t D`-path between `D`-points is already a `D`-path.  The
induction on the path keeps the invariant that the current endpoint is either
a point of `D` connected to the start inside `D`, or the vertex `t` reached
from a `D`-neighbor `D`-connected to the start; the clique hypothesis closes
the step leaving `t`.

`vcut_witness`: for `t ∉ D`, the path-form cut vertex `VCut D t` holds
exactly when `t` has two neighbors in `D` that are not `D`-connected.
Forward: the negated witness is literally the clique hypothesis.  Backward:
`b -> t -> c` through `t` inside `insert t D`.

Ordinary proofs only; no `sorry`, no new axioms beyond the permitted three.
-/

namespace CrownV

variable {n : ℕ}

/-- Symmetry of the crown adjacency `cadj`. -/
theorem bridge_cadj_symm {u v : V n} (h : cadj u v) : cadj v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

/-- Rewrite the left index of `cadj` along an equation. -/
theorem cadj_left {a b : V n} (he : a = b) {c : V n} (h : cadj a c) : cadj b c := by
  subst he
  exact h

/-- Rewrite the right index of `cadj` along an equation. -/
theorem cadj_right {b c : V n} (he : b = c) {a : V n} (h : cadj a b) : cadj a c := by
  subst he
  exact h

/-- Rerouting: under the clique hypothesis on the `D`-neighbors of `t`, every
`insert t D`-path between points of `D` is a `D`-path. -/
theorem sameC_of_clique {D : Finset (V n)} {t : V n} (htD : t ∉ D)
    (hcl : ∀ b ∈ D, ∀ c ∈ D, cadj t b → cadj t c → SameC D b c)
    {u z : V n} (hu : u ∈ D) (hz : z ∈ D)
    (h : SameC (insert t D) u z) : SameC D u z := by
  have key : ∀ w : V n, SameC (insert t D) u w →
      (w ∈ D ∧ SameC D u w) ∨
        (w = t ∧ ∃ v : V n, v ∈ D ∧ cadj t v ∧ SameC D u v) := by
    intro w hw
    induction hw with
    | refl => exact Or.inl ⟨hu, .refl⟩
    | tail _ hstep ih =>
      rcases ih with ⟨hbD, hbC⟩ | ⟨hbe, hv⟩
      · rcases Finset.mem_insert.1 hstep.2.1 with hwt | hwD
        · exact Or.inr ⟨hwt, ⟨_, hbD, bridge_cadj_symm (cadj_right hwt hstep.2.2), hbC⟩⟩
        · exact Or.inl ⟨hwD, hbC.trans (SameC.single ⟨hbD, hwD, hstep.2.2⟩)⟩
      · rcases Finset.mem_insert.1 hstep.2.1 with hwt | hwD
        · exact Or.inr ⟨hwt, hv⟩
        · obtain ⟨v, hvD, htv, hvC⟩ := hv
          exact Or.inl ⟨hwD,
            hvC.trans (hcl v hvD _ hwD htv (cadj_left hbe hstep.2.2))⟩
  rcases key z h with ⟨_, hC⟩ | ⟨heq, _⟩
  · exact hC
  · have htDm : t ∈ D := by rw [← heq]; exact hz
    exact absurd htDm htD

/-- Path-form cut vertex iff two `D`-neighbors of `t` are `D`-disconnected. -/
theorem vcut_witness {D : Finset (V n)} {t : V n} (htD : t ∉ D) :
    VCut D t ↔ ∃ b c : V n, b ∈ D ∧ c ∈ D ∧ cadj t b ∧ cadj t c ∧ ¬ SameC D b c := by
  classical
  constructor
  · intro hvc
    by_contra hno
    have hcl : ∀ e ∈ D, ∀ f ∈ D, cadj t e → cadj t f → SameC D e f := by
      intro e he f hf hte htf
      by_contra hne
      exact hno ⟨e, f, he, hf, hte, htf, hne⟩
    obtain ⟨x, y, hx, hy, hconn, hdis⟩ := hvc
    exact hdis (sameC_of_clique htD hcl hx hy hconn)
  · rintro ⟨b, c, hb, hc, htb, htc, hdis⟩
    have hbt : SameC (insert t D) b t :=
      SameC.single ⟨Finset.mem_insert_of_mem hb, Finset.mem_insert_self t D,
        bridge_cadj_symm htb⟩
    have hct : SameC (insert t D) t c :=
      SameC.single ⟨Finset.mem_insert_self t D, Finset.mem_insert_of_mem hc, htc⟩
    exact ⟨b, c, hb, hc, hbt.trans hct, hdis⟩

end CrownV

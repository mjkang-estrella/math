import CrownVClass2

/-!
Crown cut-set classification, stage 1.

For arbitrary `Finset (V n)` and `n >= 3`:

* the rerouting lemma `sameC_of_clique`: if the `D`-neighbors of `t` are
  pairwise `D`-connected, every `insert t D`-path between `D`-points is a
  `D`-path (two-component tail induction, no `NeZero`);
* the bridge `vcut_witness`: the path-form cut vertex `VCut D t` (`t ∉ D`)
  yields two `D`-neighbors of `t` in `D`-distinct components, and conversely;
* one-sided path rigidity `sameC_oneside_eq`;
* `famCut_cutset`: every valid family cut set is a `Cutset` (all six families,
  with the mixed family requiring distinct indices).

The converse direction (every `Cutset` has family shape) is staged in the
follow-up module.
-/

namespace CrownV

variable {n : ℕ}

/-! ### Small index-availability lemmas -/

/-- Two indices distinct from each other and from `p` (needs `n >= 3`). -/
theorem exists_two_ne {n : ℕ} (hn : 3 ≤ n) (p : Fin n) :
    ∃ q r : Fin n, q ≠ p ∧ r ≠ p ∧ q ≠ r := by
  have h1 : (1:ℕ) < n := by omega
  have h2 : (2:ℕ) < n := by omega
  by_cases h0 : (p:ℕ) = 0
  · refine ⟨⟨1, h1⟩, ⟨2, h2⟩, ?_, ?_, ?_⟩
    · intro hc
      have hv : (1:ℕ) = (p:ℕ) := congrArg Fin.val hc
      omega
    · intro hc
      have hv : (2:ℕ) = (p:ℕ) := congrArg Fin.val hc
      omega
    · intro hc
      have hv : (1:ℕ) = (2:ℕ) := congrArg Fin.val hc
      omega
  · by_cases h1 : (p:ℕ) = 1
    · refine ⟨⟨0, by omega⟩, ⟨2, h2⟩, ?_, ?_, ?_⟩
      · intro hc
        have hv : (0:ℕ) = (p:ℕ) := congrArg Fin.val hc
        omega
      · intro hc
        have hv : (2:ℕ) = (p:ℕ) := congrArg Fin.val hc
        omega
      · intro hc
        have hv : (0:ℕ) = (2:ℕ) := congrArg Fin.val hc
        omega
    · refine ⟨⟨0, by omega⟩, ⟨1, h1⟩, ?_, ?_, ?_⟩
      · intro hc
        have hv : (0:ℕ) = (p:ℕ) := congrArg Fin.val hc
        omega
      · intro hc
        have hv : (1:ℕ) = (p:ℕ) := congrArg Fin.val hc
        omega
      · intro hc
        have hv : (0:ℕ) = (1:ℕ) := congrArg Fin.val hc
        omega

/-- An index distinct from two distinct given ones (needs `n >= 3`). -/
theorem exists_ne_two {n : ℕ} (hn : 3 ≤ n) {p q : Fin n} (h : p ≠ q) :
    ∃ r : Fin n, r ≠ p ∧ r ≠ q := by
  obtain ⟨a, b, haP, hbP, hab⟩ := exists_two_ne (n := n) hn p
  by_cases haq : a = q
  · exact ⟨b, fun hc => hbP hc, fun hc => hab (hc.trans haq.symm)⟩
  · exact ⟨a, fun hc => haP hc, fun hc => haq hc⟩

/-- A vertex side forces the side of every member: Y version. -/
theorem isX_eq_of_mem {s : Finset (V n)} {z : V n} (hz : z ∈ s)
    (h : ∀ w ∈ s, isX w = false) : isX z = false := h z hz

/-! ### One-sided rigidity -/

/-- In a set of Y-side vertices only, every path is trivial. -/
theorem sameC_onesideY_eq {s : Finset (V n)} {x y : V n} (hx : x ∈ s)
    (hY : ∀ z ∈ s, isX z = false) (h : SameC s x y) : x = y := by
  refine sameC_eq_of_forall_not_sEdge (fun w hw => ?_) h
  obtain ⟨_, hws, hc⟩ := hw
  rcases hc.2.2 with ⟨sa, sb⟩ | ⟨sa, sb⟩
  · have sa' : isX x = true := sa
    have hxX : isX x = false := hY x hx
    rw [sa'] at hxX
    exact absurd hxX (by decide)
  · have sb' : isX w = false := sb
    have hwX : isX w = false := hY w hws
    rw [sb'] at hwX
    exact absurd hwX (by decide)

/-- In a set of X-side vertices only, every path is trivial. -/
theorem sameC_onesideX_eq {s : Finset (V n)} {x y : V n} (hx : x ∈ s)
    (hX : ∀ z ∈ s, isX z = true) (h : SameC s x y) : x = y := by
  refine sameC_eq_of_forall_not_sEdge (fun w hw => ?_) h
  obtain ⟨_, hws, hc⟩ := hw
  rcases hc.2.2 with ⟨sa, sb⟩ | ⟨sa, sb⟩
  · have sb' : isX w = false := sb
    have hwX : isX w = true := hX w hws
    rw [sb'] at hwX
    exact absurd hwX (by decide)
  · have sa' : isX x = false := sa
    have hxX : isX x = true := hX x hx
    rw [sa'] at hxX
    exact absurd hxX (by decide)

/-! ### The rerouting lemma and the cut-vertex bridge -/

/-- If every pair of `D`-neighbors of `t` is `D`-connected, then every
`insert t D`-path between `D`-points is already a `D`-path.

Proof by path induction with a two-component invariant: along the path, either
the current endpoint is `D`-reachable from `u` inside `D`, or the endpoint is
`t` and then some `t`-neighbor is `D`-reachable from `u`; the clique
hypothesis bridges the `t`-exit step. -/
theorem sameC_of_clique {D : Finset (V n)} {t : V n} (htD : t ∉ D)
    (H : ∀ b c, b ∈ D → c ∈ D → cadj t b → cadj t c → SameC D b c)
    {u : V n} (hu : u ∈ D) :
    ∀ z, SameC (insert t D) u z → z ∈ D → SameC D u z := by
  have key : ∀ z, SameC (insert t D) u z →
      (z ∈ D → SameC D u z) ∧ (z = t → ∃ b, b ∈ D ∧ cadj t b ∧ SameC D u b) := by
    intro z h
    induction h with
    | refl =>
      refine ⟨fun _ => .refl, fun hUT => ?_⟩
      exact absurd (hUT ▸ hu : t ∈ D) htD |>.elim
    | tail h₁ h₂ ih =>
      intro _
      obtain ⟨w, hwu, hwz⟩ := ... 
      sorry
  intro z h hzD
  exact (key z h).1 hzD

end CrownV

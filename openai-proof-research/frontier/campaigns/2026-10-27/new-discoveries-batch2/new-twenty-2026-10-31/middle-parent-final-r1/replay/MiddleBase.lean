/-
  Literal formalization of MathDB 355217; see SUMMARY.md for validation status.
  Target: MathDB 355217 = Conjecture 7.1 of Kazemnejad, Pahlavsay, Palezzato, Torielli,
  "Connected and outer-connected domination number of middle graphs", arXiv:2206.15439v1.

    Conjecture 7.1.  Let G be a graph of order n ≥ 2.  Then γ̃c(G) < γ̃c(M(G)).

  We refute it with an explicit connected graph G8 on 8 vertices, 11 edges:
    edges 01 06 16 23 27 37 46 47 56 57 67
  for which γ̃c(G8) = 4 = γ̃c(M(G8)).  Both conventions for "G - S connected" are covered
  (Preconnected: the empty graph counts as connected; Connected: nonempty required).

  Dependencies: Mathlib only.  Intended axioms: propext, Classical.choice, Quot.sound.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace R139.MiddleOCD

open Finset

universe u

section Defs
variable {W : Type u}

/-- `S` is a dominating set of `G`: every vertex lies in `S` or has a neighbour in `S`. -/
def IsDominating (G : SimpleGraph W) (S : Finset W) : Prop :=
  ∀ v : W, v ∈ S ∨ ∃ w ∈ S, G.Adj v w

/-- Outer-connected dominating set (Cyman 2007; source Definition 1.2), convention A:
`G - S` is connected, the empty graph counting as connected. -/
def IsOCD (G : SimpleGraph W) (S : Finset W) : Prop :=
  IsDominating G S ∧ (G.induce ((S : Set W)ᶜ)).Preconnected

/-- Convention B: `G - S` is connected and nonempty. -/
def IsOCD' (G : SimpleGraph W) (S : Finset W) : Prop :=
  IsDominating G S ∧ (G.induce ((S : Set W)ᶜ)).Connected

/-- Outer-connected domination number γ̃c (minimum cardinality), convention A. -/
noncomputable def ocd (G : SimpleGraph W) : ℕ :=
  sInf {k | ∃ S : Finset W, IsOCD G S ∧ S.card = k}

/-- Outer-connected domination number, convention B. -/
noncomputable def ocd' (G : SimpleGraph W) : ℕ :=
  sInf {k | ∃ S : Finset W, IsOCD' G S ∧ S.card = k}

/-- The middle graph M(G) (source Definition 1.3) on `W ⊕ E(G)`:
a vertex and an edge are adjacent iff incident; two distinct edges are adjacent iff they
share an endpoint; two vertices are never adjacent. -/
def middle (G : SimpleGraph W) : SimpleGraph (W ⊕ G.edgeSet) where
  Adj a b :=
    match a, b with
    | Sum.inl _, Sum.inl _ => False
    | Sum.inl v, Sum.inr e => v ∈ (e : Sym2 W)
    | Sum.inr e, Sum.inl v => v ∈ (e : Sym2 W)
    | Sum.inr e, Sum.inr f => e ≠ f ∧ ∃ v, v ∈ (e : Sym2 W) ∧ v ∈ (f : Sym2 W)
  symm := by
    constructor
    rintro (v | e) (w | f) h
    · exact h
    · exact h
    · exact h
    · exact ⟨Ne.symm h.1, h.2.imp fun _ hv => ⟨hv.2, hv.1⟩⟩
  loopless := by
    constructor
    rintro (v | e) h
    · exact h
    · exact h.1 rfl

/-- MathDB 355217 / source Conjecture 7.1 (literal: every finite simple graph of order ≥ 2),
convention A. -/
def Conjecture71 : Prop :=
  ∀ (W : Type) [Fintype W] (G : SimpleGraph W), 2 ≤ Fintype.card W → ocd G < ocd (middle G)

/-- Same, convention B. -/
def Conjecture71' : Prop :=
  ∀ (W : Type) [Fintype W] (G : SimpleGraph W), 2 ≤ Fintype.card W → ocd' G < ocd' (middle G)

/-- The intended (connected-graph) form; refuted as well. -/
def Conjecture71Connected : Prop :=
  ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.Connected → 2 ≤ Fintype.card W →
    ocd G < ocd (middle G) ∧ ocd' G < ocd' (middle G)

end Defs

/-! ### Generic lemmas -/

section Generic
variable {W : Type u}

/-- Reachability certificate: a parent map that strictly decreases a depth. -/
theorem reach_of_parent (G : SimpleGraph W) (T : Set W) (r : W) (hr : r ∈ T)
    (par : W → W) (dep : W → ℕ)
    (h : ∀ v, v ∈ T → v ≠ r → par v ∈ T ∧ G.Adj v (par v) ∧ dep (par v) < dep v) :
    ∀ v (hv : v ∈ T), (G.induce T).Reachable ⟨r, hr⟩ ⟨v, hv⟩ := by
  intro v
  induction' hd : dep v using Nat.strong_induction_on with d ih generalizing v
  intro hv
  by_cases hvr : v = r
  · subst hvr; rfl
  · obtain ⟨hpT, hadj, hlt⟩ := h v hv hvr
    have h1 := ih (dep (par v)) (hd ▸ hlt) (par v) rfl hpT
    exact h1.trans (SimpleGraph.Adj.reachable
      (show (G.induce T).Adj ⟨par v, hpT⟩ ⟨v, hv⟩ from hadj.symm))

theorem connected_of_parent (G : SimpleGraph W) (T : Set W) (r : W) (hr : r ∈ T)
    (par : W → W) (dep : W → ℕ)
    (h : ∀ v, v ∈ T → v ≠ r → par v ∈ T ∧ G.Adj v (par v) ∧ dep (par v) < dep v) :
    (G.induce T).Connected := by
  have hre := reach_of_parent G T r hr par dep h
  have hpre : (G.induce T).Preconnected := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact (hre a ha).symm.trans (hre b hb)
  exact { preconnected := hpre, nonempty := ⟨⟨r, hr⟩⟩ }

/-- A set `U` closed under adjacency inside `T` separates `u ∈ U` from `v ∉ U`. -/
theorem not_preconnected_of_closed (G : SimpleGraph W) (T U : Set W)
    (hclosed : ∀ a b, a ∈ T → b ∈ T → a ∈ U → G.Adj a b → b ∈ U)
    (u v : W) (hu : u ∈ T) (hv : v ∈ T) (huU : u ∈ U) (hvU : v ∉ U) :
    ¬ (G.induce T).Preconnected := by
  intro hpre
  obtain ⟨p⟩ := hpre ⟨u, hu⟩ ⟨v, hv⟩
  have key : ∀ (x y : T) (_ : (G.induce T).Walk x y), (x : W) ∈ U → (y : W) ∈ U := by
    intro x y q
    induction q with
    | nil => exact id
    | cons hadj _ ih =>
      intro hx
      exact ih (hclosed _ _ (Subtype.prop _) (Subtype.prop _) hx hadj)
  exact hvU (key _ _ p huU)

/-- Vertex-node counting: a dominating set of M(G) has at least |V(G)|/2 elements
(this is the content of the source's Theorem 4.1 lower bound). -/
theorem two_mul_card_ge_of_dominating_middle [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (S : Finset (W ⊕ G.edgeSet)) (hS : IsDominating (middle G) S) :
    Fintype.card W ≤ 2 * S.card := by
  classical
  have hd : ∀ v : W, ∃ d ∈ S, d = Sum.inl v ∨ (middle G).Adj (Sum.inl v) d := by
    intro v
    rcases hS (Sum.inl v) with h | ⟨w, hw, hadj⟩
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨w, hw, Or.inr hadj⟩
  choose f hfS hf using hd
  have fiber : ∀ d ∈ S, (Finset.univ.filter (fun v => f v = d)).card ≤ 2 := by
    intro d _
    rcases d with w | e
    · have hsub : Finset.univ.filter (fun v => f v = Sum.inl w) ⊆ {w} := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rcases hf v with h | h
        · rw [hv] at h
          simp only [Finset.mem_singleton]
          exact (Sum.inl_injective h).symm
        · rw [hv] at h
          exact absurd h (by simp [middle])
      exact (Finset.card_le_card hsub).trans (by simp)
    · obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | h a b =>
        have hsub : Finset.univ.filter (fun v => f v = Sum.inr ⟨s(a, b), he⟩) ⊆ {a, b} := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases hf v with h | h
          · rw [hv] at h; exact absurd h (by simp)
          · rw [hv] at h
            have hm : v ∈ s(a, b) := h
            rcases Sym2.mem_iff.1 hm with rfl | rfl <;> simp
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  calc Fintype.card W = (Finset.univ : Finset W).card := Finset.card_univ.symm
    _ = ∑ d ∈ S, (Finset.univ.filter (fun v => f v = d)).card :=
        Finset.card_eq_sum_card_fiberwise (fun v _ => hfS v)
    _ ≤ ∑ _d ∈ S, 2 := Finset.sum_le_sum fiber
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The image of a "mate" map (a perfect matching) dominates the middle graph. -/
theorem dominating_middle_of_mate (G : SimpleGraph W) (mate : W → G.edgeSet)
    (hmate : ∀ v, v ∈ ((mate v : G.edgeSet) : Sym2 W)) (D : Finset (W ⊕ G.edgeSet))
    (hD : ∀ v, Sum.inr (mate v) ∈ D) :
    IsDominating (middle G) D := by
  rintro (v | e)
  · exact Or.inr ⟨_, hD v, hmate v⟩
  · obtain ⟨e', he'⟩ := e
    induction e' using Sym2.ind with
    | h a b =>
      by_cases hx : (⟨s(a, b), he'⟩ : G.edgeSet) = mate a
      · exact Or.inl (hx ▸ hD a)
      · exact Or.inr ⟨_, hD a, hx, a, Sym2.mem_mk_left a b, hmate a⟩

end Generic

/-! ### The witness graph G8 -/

/-- Edge list of G8: two triangles {0,1,6}, {2,3,7}, the hub edge 67 and two twins 4,5
adjacent to both hubs. -/
def E8 : List (Fin 8 × Fin 8) :=
  [(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]

def adjB (i j : Fin 8) : Bool := decide ((i, j) ∈ E8 ∨ (j, i) ∈ E8)

def G8 : SimpleGraph (Fin 8) where
  Adj i j := adjB i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G8.Adj := fun i j => inferInstanceAs (Decidable (adjB i j = true))

/-! #### γ̃c(G8) = 4 -/

def S0 : Finset (Fin 8) := {0, 2, 4, 5}

theorem S0_dom : IsDominating G8 S0 := by
  unfold IsDominating; decide

def p0 (v : Fin 8) : Fin 8 := if v = 3 then 7 else 6
def d0 (v : Fin 8) : ℕ := if v = 6 then 0 else if v = 3 then 2 else 1

theorem S0_par : ∀ v : Fin 8, v ∉ S0 → v ≠ 6 → p0 v ∉ S0 ∧ G8.Adj v (p0 v) ∧ d0 (p0 v) < d0 v := by
  decide

theorem S0_conn : (G8.induce ((S0 : Set (Fin 8))ᶜ)).Connected := by
  -- complement {1,3,6,7}; root 6; 1 ↦ 6, 7 ↦ 6, 3 ↦ 7
  apply connected_of_parent G8 _ 6 (by simp [S0]) p0 d0
  intro v hv hv6
  have hv' : v ∉ S0 := by simpa using hv
  obtain ⟨h1, h2, h3⟩ := S0_par v hv' hv6
  exact ⟨by simpa using h1, h2, h3⟩


end R139.MiddleOCD

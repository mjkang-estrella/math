/-
  UNCOMPILED DRAFT (Claude lane r139; Lean was not run in this lane by instruction).
  Target: MathDB 355217 = Conjecture 7.1 of Kazemnejad, Pahlavsay, Palezzato, Torielli,
  "Connected and outer-connected domination number of middle graphs", arXiv:2206.15439v1.

    Conjecture 7.1.  Let G be a graph of order n ≥ 2.  Then γ̃c(G) < γ̃c(M(G)).

  We refute it with an explicit connected graph G8 on 8 vertices, 11 edges:
    edges 01 06 16 23 27 37 46 47 56 57 67
  for which γ̃c(G8) = 4 = γ̃c(M(G8)).  Both conventions for "G - S connected" are covered
  (Preconnected: the empty graph counts as connected; Connected: nonempty required).

  Dependencies: Mathlib only.  Intended axioms: propext, Classical.choice, Quot.sound.
  No sorry / native_decide.  Places where kernel `decide` may be slow are marked PERF.
-/
import Mathlib

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
    rintro (v | e) (w | f) h
    · exact h
    · exact h
    · exact h
    · exact ⟨Ne.symm h.1, h.2.imp fun _ hv => ⟨hv.2, hv.1⟩⟩
  loopless := by
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
  symm := by unfold Symmetric; decide
  loopless := by unfold Irreflexive; decide

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

/-- Closure of `{u}` inside the complement of `S` (8 rounds suffice on 8 vertices). -/
def stepCl (S U : Finset (Fin 8)) : Finset (Fin 8) :=
  U ∪ Finset.univ.filter (fun b => b ∉ S ∧ ∃ a ∈ U, adjB a b = true)

def cl (S : Finset (Fin 8)) (u : Fin 8) : Finset (Fin 8) := (stepCl S)^[8] {u}

/-- Boolean certificate that `S` is not outer-connected dominating. -/
def badCert (S : Finset (Fin 8)) : Prop :=
  (¬ ∀ v : Fin 8, v ∈ S ∨ ∃ w ∈ S, adjB v w = true) ∨
  ∃ u v : Fin 8, u ∉ S ∧ v ∉ S ∧ u ∈ cl S u ∧ v ∉ cl S u ∧
    ∀ a b : Fin 8, a ∉ S → b ∉ S → a ∈ cl S u → adjB a b = true → b ∈ cl S u

instance (S : Finset (Fin 8)) : Decidable (badCert S) := by unfold badCert; infer_instance

/-- PERF: kernel enumeration of the 93 subsets of size ≤ 3 of `Fin 8`. -/
theorem all_small_bad : ∀ S : Finset (Fin 8), S.card ≤ 3 → badCert S := by
  decide

theorem badCert_not_ocd (S : Finset (Fin 8)) (h : badCert S) : ¬ IsOCD G8 S := by
  rintro ⟨hdom, hpre⟩
  rcases h with hnd | ⟨u, v, hu, hv, huU, hvU, hcl⟩
  · exact hnd hdom
  · exact not_preconnected_of_closed G8 _ (↑(cl S u)) (fun a b ha hb haU hab => hcl a b
      (by simpa using ha) (by simpa using hb) haU hab) u v (by simpa using hu) (by simpa using hv)
      huU hvU hpre

theorem ocd_G8_lower (S : Finset (Fin 8)) (h : IsOCD G8 S) : 4 ≤ S.card := by
  by_contra hlt
  exact badCert_not_ocd S (all_small_bad S (by omega)) h

theorem ocd'_G8_lower (S : Finset (Fin 8)) (h : IsOCD' G8 S) : 4 ≤ S.card :=
  ocd_G8_lower S ⟨h.1, h.2.preconnected⟩

theorem ocd_G8 : ocd G8 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨S0, ⟨S0_dom, S0_conn.preconnected⟩, by decide⟩
  · exact le_csInf ⟨4, S0, ⟨S0_dom, S0_conn.preconnected⟩, by decide⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_G8_lower S hS)

theorem ocd'_G8 : ocd' G8 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨S0, ⟨S0_dom, S0_conn⟩, by decide⟩
  · exact le_csInf ⟨4, S0, ⟨S0_dom, S0_conn⟩, by decide⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd'_G8_lower S hS)

/-! #### γ̃c(M(G8)) = 4 -/

/-- Edge of G8 from a Bool-certified pair. -/
def ed (a b : Fin 8) (h : adjB a b = true) : G8.edgeSet := ⟨s(a, b), (G8.mem_edgeSet).2 h⟩

/-- Perfect matching F = {01, 23, 46, 57}. -/
def mate : Fin 8 → G8.edgeSet := fun v =>
  if v = 0 ∨ v = 1 then ed 0 1 rfl
  else if v = 2 ∨ v = 3 then ed 2 3 rfl
  else if v = 4 ∨ v = 6 then ed 4 6 rfl
  else ed 5 7 rfl

theorem mate_mem : ∀ v, v ∈ ((mate v : G8.edgeSet) : Sym2 (Fin 8)) := by
  decide  -- PERF: unfolds `ed`, Sym2 membership on Fin 8; fallback: `intro v; fin_cases v <;> simp [mate, ed]`

def D8 : Finset (Fin 8 ⊕ G8.edgeSet) :=
  {Sum.inr (ed 0 1 rfl), Sum.inr (ed 2 3 rfl), Sum.inr (ed 4 6 rfl), Sum.inr (ed 5 7 rfl)}

theorem D8_mate : ∀ v, Sum.inr (mate v) ∈ D8 := by
  intro v; fin_cases v <;> simp [mate, D8]

theorem D8_card : D8.card = 4 := by
  -- the four edges are distinct elements of Sym2 (Fin 8)
  decide  -- PERF/fallback: `simp [D8, ed, Sym2.eq_iff]`

theorem D8_dom : IsDominating (middle G8) D8 :=
  dominating_middle_of_mate G8 mate mate_mem D8 D8_mate

/-- Depth of a vertex in the spanning tree of G8 - F rooted at 6
(tree edges 06 16 56 67 27 37 47). -/
def dv (v : Fin 8) : ℕ := if v = 6 then 0 else if v = 2 ∨ v = 3 ∨ v = 4 then 2 else 1

/-- Tree parent in G8 - F. -/
def tp (v : Fin 8) : Fin 8 := if v = 2 ∨ v = 3 ∨ v = 4 then 7 else 6

/-- Key used to pick the shallower endpoint of an edge (injective). -/
def key (v : Fin 8) : ℕ := 8 * dv v + v.val

theorem key_inj : ∀ a b : Fin 8, key a = key b → a = b := by decide

/-- The endpoint of smaller key (the one closer to the root 6). -/
def lowEnd (e : Sym2 (Fin 8)) : Fin 8 :=
  Sym2.lift ⟨fun a b => if key a ≤ key b then a else b, fun a b => by
    by_cases h1 : key a ≤ key b <;> by_cases h2 : key b ≤ key a
    · rw [if_pos h1, if_pos h2]; exact key_inj a b (le_antisymm h1 h2)
    · rw [if_pos h1, if_neg h2]
    · rw [if_neg h1, if_pos h2]
    · omega⟩ e

theorem lowEnd_mem (e : Sym2 (Fin 8)) : lowEnd e ∈ e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [lowEnd, Sym2.lift_mk]
    split_ifs
    · exact Sym2.mem_mk_left a b
    · exact Sym2.mem_mk_right a b

/-- Parent map on M(G8) - D8 towards the root `inl 6`. -/
def parM : Fin 8 ⊕ G8.edgeSet → Fin 8 ⊕ G8.edgeSet
  | Sum.inl v => if h : adjB v (tp v) = true then Sum.inr (ed v (tp v) h) else Sum.inl v
  | Sum.inr e => Sum.inl (lowEnd (e : Sym2 (Fin 8)))

def depM : Fin 8 ⊕ G8.edgeSet → ℕ
  | Sum.inl v => 2 * dv v
  | Sum.inr e => 2 * dv (lowEnd (e : Sym2 (Fin 8))) + 1

/-- Tree edges 06 16 56 67 27 37 47 are edges of G8 and avoid the matching. -/
theorem tree_ok : ∀ w : Fin 8, w ≠ 6 →
    ∃ h : adjB w (tp w) = true, Sum.inr (ed w (tp w) h) ∉ D8 ∧
      2 * dv (lowEnd s(w, tp w)) + 1 < 2 * dv w := by
  -- PERF/fallback: `intro w hw; fin_cases w <;> simp_all <;> decide`
  decide

theorem M8_conn : ((middle G8).induce ((D8 : Set (Fin 8 ⊕ G8.edgeSet))ᶜ)).Connected := by
  apply connected_of_parent (middle G8) _ (Sum.inl 6) (by simp [D8]) parM depM
  rintro (w | e) hT hne
  · have hw : w ≠ 6 := fun h => hne (by rw [h])
    obtain ⟨h, hnot, hlt⟩ := tree_ok w hw
    have hp : parM (Sum.inl w) = Sum.inr (ed w (tp w) h) := by simp [parM, h]
    rw [hp]
    refine ⟨by simpa using hnot, ?_, ?_⟩
    · -- adjacency vertex–edge is incidence
      show w ∈ s(w, tp w)
      exact Sym2.mem_mk_left _ _
    · simpa [depM, ed] using hlt
  · refine ⟨?_, ?_, ?_⟩
    · simp [parM, D8]
    · show lowEnd (e : Sym2 (Fin 8)) ∈ (e : Sym2 (Fin 8))
      exact lowEnd_mem _
    · simp [parM, depM]

theorem G8_par : ∀ v : Fin 8, v ≠ 6 → G8.Adj v (tp v) ∧ dv (tp v) < dv v := by decide

theorem G8_connected : G8.Connected := by
  have h := connected_of_parent G8 Set.univ 6 (Set.mem_univ _) tp dv
    (fun v _ hv => ⟨Set.mem_univ _, (G8_par v hv).1, (G8_par v hv).2⟩)
  exact (SimpleGraph.induceUnivIso G8).connected_iff.mp h

theorem ocd_M8_lower (S : Finset (Fin 8 ⊕ G8.edgeSet)) (h : IsDominating (middle G8) S) :
    4 ≤ S.card := by
  have := two_mul_card_ge_of_dominating_middle G8 S h
  simp only [Fintype.card_fin] at this
  omega

theorem ocd_M8 : ocd (middle G8) = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨D8, ⟨D8_dom, M8_conn.preconnected⟩, D8_card⟩
  · exact le_csInf ⟨4, D8, ⟨D8_dom, M8_conn.preconnected⟩, D8_card⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_M8_lower S hS.1)

theorem ocd'_M8 : ocd' (middle G8) = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨D8, ⟨D8_dom, M8_conn⟩, D8_card⟩
  · exact le_csInf ⟨4, D8, ⟨D8_dom, M8_conn⟩, D8_card⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_M8_lower S hS.1)

/-! ### Endpoints -/

/-- MathDB 355217 is false (convention A). -/
theorem conjecture71_false : ¬ Conjecture71 := by
  intro h
  have := h (Fin 8) G8 (by simp)
  rw [ocd_G8, ocd_M8] at this
  exact lt_irrefl _ this

/-- MathDB 355217 is false (convention B). -/
theorem conjecture71'_false : ¬ Conjecture71' := by
  intro h
  have := h (Fin 8) G8 (by simp)
  rw [ocd'_G8, ocd'_M8] at this
  exact lt_irrefl _ this

/-- Even restricted to connected graphs the conjecture fails. -/
theorem conjecture71Connected_false : ¬ Conjecture71Connected := by
  intro h
  have := (h (Fin 8) G8 G8_connected (by simp)).1
  rw [ocd_G8, ocd_M8] at this
  exact lt_irrefl _ this

end R139.MiddleOCD

# Complete Lean source appendix — COMPLETE

All modules below are included in dependency order. Each block is byte-identical
to its file in `src/`. The literal classification endpoint is proved in BetweennessClassification.lean.

### `BetweennessDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

noncomputable def sigma (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) : ℕ := (G.finsetWalkLength (G.dist v w) v w).card

noncomputable def sigmaThrough (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w x : Fin n) : ℕ :=
  ((G.finsetWalkLength (G.dist v w) v w).filter
    (fun p => x ∈ p.support ∧ x ≠ v ∧ x ≠ w)).card

noncomputable def betweenness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n) : ℚ :=
  ∑ v, ∑ w, if v < w then (sigmaThrough G v w x : ℚ) / sigma G v w else 0

def LowBUG (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ (∀ x y, betweenness G x = betweenness G y) ∧
    (∀ x, betweenness G x < 1)

def StarComponent (F : SimpleGraph (Fin n)) (l : ℕ) (K : F.ConnectedComponent) : Prop :=
  ∃ c ∈ K.supp, K.supp.ncard = l + 1 ∧
    ∀ u ∈ K.supp, ∀ v ∈ K.supp,
      (F.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c))

def EqualStarUnion (F : SimpleGraph (Fin n)) : Prop :=
  ∃ l : ℕ, ∀ K : F.ConnectedComponent, StarComponent F l K

def DiameterTwo (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v, u = v ∨ G.Adj u v ∨ ∃ x, G.Adj u x ∧ G.Adj x v

def close (F : SimpleGraph (Fin n)) (x a b : Fin n) : Prop :=
  F.Adj x a ∨ F.Adj x b
instance (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x a b : Fin n) :
    Decidable (close F x a b) := inferInstanceAs (Decidable (_ ∨ _))

def closeVertices (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) :
    Finset (Fin n) := Finset.univ.filter (fun x => close F x a b)
def pole (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) : ℕ :=
  (closeVertices F a b).card

def pairs (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ F.Adj e.1 e.2)
def closeEdges (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n) :=
  (pairs F).filter (fun e => close F x e.1 e.2)
def componentEdges (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) : Finset (Fin n × Fin n) := by
  classical
  exact (pairs F).filter (fun e => e.1 ∈ K.supp)

def weight (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) : ℚ :=
  1 / ((n : ℚ) - pole F a b)
def coBetweenness (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n) : ℚ :=
  ∑ e ∈ closeEdges F x, weight F e.1 e.2

lemma sigma_pos (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.Connected) (v w : Fin n) : 0 < sigma G v w := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v w
  exact Finset.card_pos.mpr ⟨p, SimpleGraph.mem_finsetWalkLength_iff.mpr hp⟩

lemma shortest_isPath (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} {p : G.Walk v w}
    (hp : p ∈ G.finsetWalkLength (G.dist v w) v w) : p.IsPath :=
  p.isPath_of_length_eq_dist (SimpleGraph.mem_finsetWalkLength_iff.mp hp)

#print axioms sigma_pos
#print axioms shortest_isPath
end Betweenness
```

### `BetweennessCounting.lean`

```lean
import BetweennessDefinitions
import Mathlib.Tactic.FinCases

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma sigma_eq_commonNeighbors {v w : Fin n} (h : G.dist v w = 2) :
    sigma G v w = Fintype.card (G.commonNeighbors v w) := by
  rw [sigma, h, ← SimpleGraph.card_set_walk_length_eq]
  exact Fintype.card_congr (G.walkLengthTwoEquivCommonNeighbors v w)

omit [DecidableRel G.Adj] in
lemma walk_two_internal {v w x : Fin n} (p : G.Walk v w) (hp : p.length = 2) :
    (x ∈ p.support ∧ x ≠ v ∧ x ≠ w) ↔ p.snd = x := by
  match p, hp with
  | .cons ha (.cons hb .nil), _ =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false, SimpleGraph.Walk.snd_cons]
    constructor
    · rintro ⟨hh, hv, hw⟩
      rcases hh with hh | hh | hh
      · exact (hv hh).elim
      · exact hh.symm
      · exact (hw hh).elim
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl), ha.ne.symm, hb.ne⟩

lemma sigmaThrough_eq_of_dist_two {v w x : Fin n} (h : G.dist v w = 2) :
    sigmaThrough G v w x = if G.Adj v x ∧ G.Adj x w then 1 else 0 := by
  classical
  rw [sigmaThrough, h]
  split_ifs with hx
  · let p : G.Walk v w := .cons hx.1 (.cons hx.2 .nil)
    have hs : (G.finsetWalkLength 2 v w).filter
        (fun q => x ∈ q.support ∧ x ≠ v ∧ x ≠ w) = {p} := by
      ext q
      simp only [Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hi⟩
        have hs := (walk_two_internal G q hq).mp hi
        match q, hq with
        | .cons ha (.cons hb .nil), _ =>
          simp only [SimpleGraph.Walk.snd_cons] at hs
          subst x
          rfl
      · rintro rfl
        exact ⟨rfl, (walk_two_internal G p rfl).mpr rfl⟩
    rw [hs, Finset.card_singleton]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hi⟩ := Finset.mem_filter.mp hp
    have hl := SimpleGraph.mem_finsetWalkLength_iff.mp hp
    have hs := (walk_two_internal G p hl).mp hi
    have hc := (G.walkLengthTwoEquivCommonNeighbors v w ⟨p, hl⟩).property
    change G.Adj v p.snd ∧ G.Adj w p.snd at hc
    rw [hs] at hc
    exact hx ⟨hc.1, hc.2.symm⟩

lemma sigmaThrough_eq_zero_of_dist_le_one {v w x : Fin n} (h : G.dist v w ≤ 1) :
    sigmaThrough G v w x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, hi⟩ := Finset.mem_filter.mp hp
  have hl := SimpleGraph.mem_finsetWalkLength_iff.mp hp
  cases p with
  | nil => simp at hi
  | cons ha q =>
    cases q with
    | nil =>
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi.1 with hv | hw
      · exact hi.2.1 hv
      · exact hi.2.2 hw
    | cons hb r =>
      simp only [SimpleGraph.Walk.length_cons] at hl
      omega

omit [DecidableRel G.Adj] in
lemma diameterTwo_dist (h : DiameterTwo G) (u v : Fin n) : G.dist u v ≤ 2 := by
  rcases h u v with rfl | hadj | ⟨x, hx, hy⟩
  · simp
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]; decide
  · exact G.dist_le (.cons hx (.cons hy .nil))

omit [DecidableRel G.Adj] in
lemma diameterTwo_connected [Nonempty (Fin n)] (h : DiameterTwo G) : G.Connected := by
  refine ⟨?_⟩
  intro u v
  rcases h u v with rfl | hadj | ⟨x, hx, hy⟩
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hx.reachable.trans hy.reachable

#print axioms sigma_eq_commonNeighbors
#print axioms sigmaThrough_eq_of_dist_two
#print axioms sigmaThrough_eq_zero_of_dist_le_one
#print axioms diameterTwo_dist
#print axioms diameterTwo_connected
end Betweenness
```

### `BetweennessTotal.lean`

```lean
import BetweennessCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma internal_count {v w : Fin n} (p : G.Walk v w) (hp : p.IsPath) :
    (Finset.univ.filter (fun x => x ∈ p.support ∧ x ≠ v ∧ x ≠ w)).card =
      p.length - 1 := by
  classical
  have hs : Finset.univ.filter (fun x => x ∈ p.support ∧ x ≠ v ∧ x ≠ w) =
      (p.support.toFinset.erase v).erase w := by ext x; simp [and_comm, and_left_comm, and_assoc]
  rw [hs]
  by_cases hvw : v = w
  · subst w
    have hz : p.length = 0 := by
      exact SimpleGraph.Walk.length_eq_zero_iff.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hp)
    have hn : p = .nil := SimpleGraph.Walk.eq_nil_iff_nil.mpr (SimpleGraph.Walk.length_eq_zero_iff.mp hz)
    subst p
    simp
  · rw [Finset.card_erase_of_mem (by simp [Ne.symm hvw, p.end_mem_support]),
      Finset.card_erase_of_mem (by simp [p.start_mem_support]),
      List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
    omega

lemma sigmaThrough_sum (_h : G.Connected) (v w : Fin n) :
    ∑ x, sigmaThrough G v w x = (G.dist v w - 1) * sigma G v w := by
  classical
  unfold sigmaThrough
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hpoint : ∀ p ∈ G.finsetWalkLength (G.dist v w) v w,
      (∑ x : Fin n, if x ∈ p.support ∧ x ≠ v ∧ x ≠ w then 1 else 0) =
        G.dist v w - 1 := by
    intro p hp
    rw [← Finset.sum_filter]
    simpa [SimpleGraph.mem_finsetWalkLength_iff.mp hp] using
      internal_count G p (shortest_isPath G hp)
  rw [Finset.sum_congr rfl hpoint]
  simp [sigma, Nat.mul_comm]

lemma total_betweenness (h : G.Connected) :
    ∑ x, betweenness G x =
      ∑ v, ∑ w, if v < w then ((G.dist v w - 1 : ℕ) : ℚ) else 0 := by
  unfold betweenness
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hvw : v < w
  · simp only [hvw, ite_true]
    rw [← Finset.sum_div, ← Nat.cast_sum, sigmaThrough_sum G h, Nat.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast ne_of_gt (sigma_pos G h v w))
  · simp [hvw]

lemma complement_edge_bound (h : G.Connected) :
    ((pairs Gᶜ).card : ℚ) ≤ ∑ x, betweenness G x := by
  rw [total_betweenness G h]
  have hcount : ((pairs Gᶜ).card : ℚ) =
      ∑ v, ∑ w, if v < w ∧ Gᶜ.Adj v w then (1 : ℚ) else 0 := by
    simp only [pairs, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
    push_cast
    rfl
  rw [hcount]
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro w hw
  by_cases hvw : v < w
  · simp only [hvw, true_and, ite_true]
    split_ifs with ha
    · have hd := h.one_lt_dist_of_ne_of_not_adj (ne_of_lt hvw) ha.2
      have hd' : 1 ≤ G.dist v w - 1 := by omega
      exact_mod_cast hd'
    · positivity
  · simp [hvw]

lemma lowBUG_sparse (h : LowBUG G) : (pairs Gᶜ).card < n := by
  have hb := complement_edge_bound G h.1
  have hs : (∑ x, betweenness G x) < ∑ _x : Fin n, (1 : ℚ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · obtain ⟨v⟩ := h.1.nonempty
      exact ⟨v, Finset.mem_univ v⟩
    · intro x hx; exact h.2.2 x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hs
  exact_mod_cast lt_of_le_of_lt hb hs

#print axioms internal_count
#print axioms sigmaThrough_sum
#print axioms total_betweenness
#print axioms complement_edge_bound
#print axioms lowBUG_sparse
end Betweenness
```

### `BetweennessSimplicial.lean`

```lean
import BetweennessTotal
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- An internal vertex of a shortest walk cannot have a clique neighbourhood. -/
lemma shortest_no_internal_of_clique (x : Fin n)
    (hc : ∀ u v, G.Adj x u → G.Adj x v → u ≠ v → G.Adj u v)
    {v w : Fin n} (p : G.Walk v w) (hp : p.length = G.dist v w) :
    ¬ (x ∈ p.support ∧ x ≠ v ∧ x ≠ w) := by
  induction p with
  | nil => simp
  | @cons v u w h p ih =>
    intro hx
    have hq : p.length = G.dist u w :=
      SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_cons h)
    by_cases hxu : x = u
    · subst x
      cases p with
      | nil => exact hx.2.2 rfl
      | @cons u z w hz r =>
        have hpath := (SimpleGraph.Walk.cons h (.cons hz r)).isPath_of_length_eq_dist hp
        have hvz : v ≠ z := by
          have hn := hpath.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hn
          intro he
          exact hn.1 (by rw [he]; simp)
        have hadj := hc v z h.symm hz hvz
        have hshort := G.dist_le (SimpleGraph.Walk.cons hadj r)
        simp only [SimpleGraph.Walk.length_cons] at hp hshort
        omega
    · apply ih hq
      exact ⟨by simpa only [SimpleGraph.Walk.support_cons, List.mem_cons,
        or_iff_right hx.2.1] using hx.1, hxu, hx.2.2⟩

lemma betweenness_zero_of_clique (x : Fin n)
    (hc : ∀ u v, G.Adj x u → G.Adj x v → u ≠ v → G.Adj u v) :
    betweenness G x = 0 := by
  have ht : ∀ v w, sigmaThrough G v w x = 0 := by
    intro v w
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hi⟩ := Finset.mem_filter.mp hp
    exact shortest_no_internal_of_clique G x hc p
      (SimpleGraph.mem_finsetWalkLength_iff.mp hp) hi
  unfold betweenness
  simp only [ht, Nat.cast_zero, zero_div, ite_self, Finset.sum_const_zero]

lemma lowBUG_complete_of_zero (h : LowBUG G) (x : Fin n)
    (hx : betweenness G x = 0) : G = ⊤ := by
  have hz : ∀ y, betweenness G y = 0 := fun y => (h.2.1 y x).trans hx
  have hb := complement_edge_bound G h.1
  simp only [hz, Finset.sum_const_zero] at hb
  have hcard : (pairs Gᶜ).card = 0 := by exact_mod_cast (le_antisymm hb (Nat.cast_nonneg _))
  ext v w
  simp only [SimpleGraph.top_adj]
  constructor
  · exact fun ha => ha.ne
  · intro hne
    by_contra hna
    have hp : (pairs Gᶜ).Nonempty := by
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact ⟨(v,w), by simp [pairs, hl, SimpleGraph.compl_adj, hne, hna]⟩
      · exact ⟨(w,v), by simp [pairs, hl, SimpleGraph.compl_adj, hne.symm,
          show ¬ G.Adj w v from fun hh => hna hh.symm]⟩
    exact (Nat.ne_of_gt (Finset.card_pos.mpr hp)) hcard

#print axioms shortest_no_internal_of_clique
#print axioms betweenness_zero_of_clique
#print axioms lowBUG_complete_of_zero
end Betweenness
```

### `BetweennessLowDiameter.lean`

```lean
import BetweennessSimplicial
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma pairs_card_eq_edgeSet (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    (pairs F).card = Nat.card F.edgeSet := by
  classical
  rw [Nat.card_eq_fintype_card, ← F.edgeFinset_card]
  apply Finset.card_bij (fun e _ => s(e.1, e.2))
  · intro e he
    simpa using (Finset.mem_filter.mp he).2.2
  · intro e he f hf hef
    have he' : e.1 < e.2 := (Finset.mem_filter.mp he).2.1
    have hf' : f.1 < f.2 := (Finset.mem_filter.mp hf).2.1
    rcases Sym2.eq_iff.mp hef with hh | hh
    · exact Prod.ext hh.1 hh.2
    · rw [← hh.2, ← hh.1] at hf'
      exact (not_lt_of_ge he'.le hf').elim
  · intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : F.Adj a b := by simpa using he
      rcases lt_or_gt_of_ne hab.ne with hl | hl
      · exact ⟨(a,b), by simp [pairs, hl, hab], rfl⟩
      · exact ⟨(b,a), by simp [pairs, hl, hab.symm], Sym2.eq_swap⟩

/-- Keep just edges incident with one of two chosen centres. -/
def centreEdges (F : SimpleGraph (Fin n)) (a b : Fin n) : SimpleGraph (Fin n) where
  Adj u v := F.Adj u v ∧ (u = a ∨ u = b ∨ v = a ∨ v = b)
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

lemma centreEdges_le (F : SimpleGraph (Fin n)) (a b : Fin n) : centreEdges F a b ≤ F :=
  fun _ _ h => h.1

lemma centreEdges_connected (F : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : F.Adj a b) (hc : ∀ v, v = a ∨ v = b ∨ F.Adj a v ∨ F.Adj b v) :
    (centreEdges F a b).Connected := by
  let : Nonempty (Fin n) := ⟨a⟩
  have hra : ∀ v, (centreEdges F a b).Reachable a v := by
    intro v
    have hr : (centreEdges F a b).Adj a b := ⟨hab, Or.inl rfl⟩
    rcases hc v with rfl | rfl | ha | hb
    · exact .refl _
    · exact hr.reachable
    · exact (show (centreEdges F a b).Adj a v from ⟨ha, Or.inl rfl⟩).reachable
    · exact hr.reachable.trans (show (centreEdges F a b).Adj b v from
        ⟨hb, Or.inr (Or.inl rfl)⟩).reachable
  exact ⟨fun u v => (hra u).symm.trans (hra v)⟩

lemma lowBUG_diameterTwo (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) : DiameterTwo G := by
  classical
  by_contra hnot
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ (a = b ∨ G.Adj a b ∨ ∃ x, G.Adj a x ∧ G.Adj x b) := by
    simpa only [DiameterTwo, not_forall] using hnot
  have hne : a ≠ b := fun he => hab (Or.inl he)
  have hna : ¬G.Adj a b := fun he => hab (Or.inr (Or.inl he))
  have hFab : Gᶜ.Adj a b := ⟨hne, hna⟩
  have hc : ∀ v, v = a ∨ v = b ∨ Gᶜ.Adj a v ∨ Gᶜ.Adj b v := by
    intro v
    by_cases hva : v = a
    · exact Or.inl hva
    by_cases hvb : v = b
    · exact Or.inr (Or.inl hvb)
    by_cases hav : G.Adj a v
    · have hbv : ¬G.Adj b v := fun hh => hab (Or.inr (Or.inr ⟨v, hav, hh.symm⟩))
      exact Or.inr (Or.inr (Or.inr ⟨Ne.symm hvb, hbv⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨Ne.symm hva, hav⟩))
  have hDc := centreEdges_connected Gᶜ a b hFab hc
  have hFc : Gᶜ.Connected := hDc.mono (centreEdges_le Gᶜ a b)
  have hsp := lowBUG_sparse G h
  rw [pairs_card_eq_edgeSet] at hsp
  have hlo := hFc.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hlo
  have ht : Gᶜ.IsTree := SimpleGraph.isTree_iff_connected_and_card.mpr
    ⟨hFc, by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (show Fintype.card Gᶜ.edgeSet + 1 = n by
        rw [Nat.card_eq_fintype_card] at hsp; omega)⟩
  have heq : centreEdges Gᶜ a b = Gᶜ :=
    (SimpleGraph.isTree_iff_minimal_connected.mp ht).eq_of_le hDc (centreEdges_le Gᶜ a b)
  have hclique : ∀ u v, G.Adj a u → G.Adj a v → u ≠ v → G.Adj u v := by
    intro u v hau hav huv
    by_contra hnv
    have hfuv : Gᶜ.Adj u v := ⟨huv, hnv⟩
    rw [← heq] at hfuv
    rcases hfuv.2 with hua | hub | hva | hvb
    · exact hau.ne hua.symm
    · exact hna (hub ▸ hau)
    · exact hav.ne hva.symm
    · exact hna (hvb ▸ hav)
  have hz := betweenness_zero_of_clique G a hclique
  have htop := lowBUG_complete_of_zero G h a hz
  have : G.Adj a b := by rw [htop]; exact hne
  exact hna this

#print axioms pairs_card_eq_edgeSet
#print axioms lowBUG_diameterTwo
end Betweenness
```

### `BetweennessDiameterTwo.lean`

```lean
import BetweennessCounting
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma dist_two_of_diameterTwo (h : DiameterTwo G) {v w : Fin n}
    (hne : v ≠ w) (hna : ¬ G.Adj v w) : G.dist v w = 2 := by
  obtain he | he | ⟨x, hx, hy⟩ := h v w
  · exact (hne he).elim
  · exact (hna he).elim
  · have hr := hx.reachable.trans hy.reachable
    have hlow := hr.one_lt_dist_of_ne_of_not_adj hne hna
    have hhi := diameterTwo_dist G h v w
    omega

lemma contribution_diameterTwo (h : DiameterTwo G) {v w : Fin n}
    (hne : v ≠ w) (x : Fin n) :
    (sigmaThrough G v w x : ℚ) / sigma G v w =
      if ¬G.Adj v w ∧ G.Adj v x ∧ G.Adj x w then
        1 / (Fintype.card (G.commonNeighbors v w) : ℚ) else 0 := by
  by_cases ha : G.Adj v w
  · rw [sigmaThrough_eq_zero_of_dist_le_one G
      (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha])]
    simp [ha]
  · have hd := dist_two_of_diameterTwo G h hne ha
    rw [sigmaThrough_eq_of_dist_two G hd, sigma_eq_commonNeighbors G hd]
    by_cases hx : G.Adj v x ∧ G.Adj x w <;> simp [ha, hx]

/-- A computable diameter-two expression, proved equal to the shortest-walk definition. -/
def twoBetweenness (x : Fin n) : ℚ :=
  ∑ v, ∑ w, if v < w ∧ ¬G.Adj v w ∧ G.Adj v x ∧ G.Adj x w then
    1 / (Fintype.card (G.commonNeighbors v w) : ℚ) else 0

lemma betweenness_eq_twoBetweenness (h : DiameterTwo G) (x : Fin n) :
    betweenness G x = twoBetweenness G x := by
  unfold betweenness twoBetweenness
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hvw : v < w
  · simp only [hvw, ite_true, true_and]
    exact contribution_diameterTwo G h (ne_of_lt hvw) x
  · simp [hvw]

lemma commonNeighbors_complement {a b : Fin n} (hab : Gᶜ.Adj a b) :
    Fintype.card (G.commonNeighbors a b) = n - pole Gᶜ a b := by
  classical
  have hne : a ≠ b := hab.ne
  have hs : Finset.univ.filter (fun x => G.Adj a x ∧ G.Adj b x) =
      Finset.univ \ closeVertices Gᶜ a b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, closeVertices, close, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨ha, hb⟩
      exact fun hh => hh.elim (fun hh => hh.2 ha.symm) (fun hh => hh.2 hb.symm)
    · intro hh
      by_cases hxa : x = a
      · subst x
        exact (hh (Or.inr ⟨hne, fun hx => hab.2 hx⟩)).elim
      by_cases hxb : x = b
      · subst x
        exact (hh (Or.inl ⟨hne.symm, fun hx => hab.2 hx.symm⟩)).elim
      exact ⟨by by_contra hc; exact hh (Or.inl ⟨hxa, fun h => hc h.symm⟩),
        by by_contra hc; exact hh (Or.inr ⟨hxb, fun h => hc h.symm⟩)⟩
  have hcard : Fintype.card (G.commonNeighbors a b) =
      (Finset.univ.filter (fun x => G.Adj a x ∧ G.Adj b x)).card := by
    exact Fintype.card_ofFinset _ (by intro x; simp [SimpleGraph.mem_commonNeighbors])
  rw [hcard, hs, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [pole]

lemma pole_lt_of_diameterTwo (h : DiameterTwo G) {a b : Fin n}
    (hab : Gᶜ.Adj a b) : pole Gᶜ a b < n := by
  have hd := dist_two_of_diameterTwo G h hab.ne hab.2
  have hp : 0 < Fintype.card (G.commonNeighbors a b) := by
    rw [← sigma_eq_commonNeighbors G hd]
    apply Finset.card_pos.mpr
    obtain ⟨p, hp⟩ := (SimpleGraph.Reachable.of_dist_ne_zero (by omega : G.dist a b ≠ 0)).exists_walk_length_eq_dist
    exact ⟨p, SimpleGraph.mem_finsetWalkLength_iff.mpr hp⟩
  rw [commonNeighbors_complement G hab] at hp
  omega

#print axioms contribution_diameterTwo
#print axioms betweenness_eq_twoBetweenness
#print axioms commonNeighbors_complement
#print axioms pole_lt_of_diameterTwo
end Betweenness
```

### `BetweennessComplement.lean`

```lean
import BetweennessDiameterTwo
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma not_close_compl_iff {a b x : Fin n} (hab : Gᶜ.Adj a b) :
    ¬ close Gᶜ x a b ↔ G.Adj a x ∧ G.Adj x b := by
  simp only [close, SimpleGraph.compl_adj, not_or]
  constructor
  · rintro ⟨ha, hb⟩
    have hxa : x ≠ a := by
      intro hx; subst x
      exact hb ⟨hab.ne, hab.2⟩
    have hxb : x ≠ b := by
      intro hx; subst x
      exact ha ⟨hab.ne.symm, fun h => hab.2 h.symm⟩
    exact ⟨(not_not.mp (fun h => ha ⟨hxa, h⟩)).symm,
      not_not.mp (fun h => hb ⟨hxb, h⟩)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => h.2 ha.symm, fun h => h.2 hb⟩

lemma contribution_complement (h : DiameterTwo G) {v w : Fin n}
    (hne : v ≠ w) (x : Fin n) :
    (sigmaThrough G v w x : ℚ) / sigma G v w =
      if Gᶜ.Adj v w ∧ ¬close Gᶜ x v w then weight Gᶜ v w else 0 := by
  rw [contribution_diameterTwo G h hne]
  by_cases ha : Gᶜ.Adj v w
  · have hcard := commonNeighbors_complement G ha
    have hp := pole_lt_of_diameterTwo G h ha
    have hweight : (1 : ℚ) / Fintype.card (G.commonNeighbors v w) = weight Gᶜ v w := by
      rw [hcard, Nat.cast_sub (Nat.le_of_lt hp)]
      rfl
    simp only [ha, true_and, not_close_compl_iff G ha, ha.2, not_false_eq_true]
    split_ifs <;> simp_all

  · have hadj : G.Adj v w := by
      by_contra hn
      exact ha ⟨hne, hn⟩
    simp [ha, hadj]

lemma betweenness_eq_nonclose (h : DiameterTwo G) (x : Fin n) :
    betweenness G x = ∑ e ∈ pairs Gᶜ,
      if ¬close Gᶜ x e.1 e.2 then weight Gᶜ e.1 e.2 else 0 := by
  unfold betweenness pairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hvw : v < w
  · simp only [hvw, ite_true, true_and]
    rw [contribution_complement G h (ne_of_lt hvw)]
    by_cases ha : Gᶜ.Adj v w <;> simp [ha]
  · simp [hvw]

lemma betweenness_eq_total_sub_co (h : DiameterTwo G) (x : Fin n) :
    betweenness G x = (∑ e ∈ pairs Gᶜ, weight Gᶜ e.1 e.2) - coBetweenness Gᶜ x := by
  have hh : betweenness G x + coBetweenness Gᶜ x =
      ∑ e ∈ pairs Gᶜ, weight Gᶜ e.1 e.2 := by
    rw [betweenness_eq_nonclose G h]
    unfold coBetweenness closeEdges
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hc : close Gᶜ x e.1 e.2 <;> simp [hc]
  exact eq_sub_iff_add_eq.mpr hh

lemma uniform_iff_coUniform (h : DiameterTwo G) :
    (∀ x y, betweenness G x = betweenness G y) ↔
      (∀ x y, coBetweenness Gᶜ x = coBetweenness Gᶜ y) := by
  simp_rw [betweenness_eq_total_sub_co G h, sub_right_inj]

#print axioms contribution_complement
#print axioms betweenness_eq_total_sub_co
#print axioms uniform_iff_coUniform
end Betweenness
```

### `BetweennessReduction.lean`

```lean
import BetweennessLowDiameter
import BetweennessComplement

namespace Betweenness
variable {n : ℕ}

/-- The fully proved general reductions needed by the component classification. -/
theorem lowBUG_reduction (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) :
    DiameterTwo G ∧ (pairs Gᶜ).card < n ∧
      (∀ a b, Gᶜ.Adj a b → pole Gᶜ a b < n) ∧
      (∀ x y, coBetweenness Gᶜ x = coBetweenness Gᶜ y) := by
  have hd := lowBUG_diameterTwo G h
  exact ⟨hd, lowBUG_sparse G h,
    fun _ _ hab => pole_lt_of_diameterTwo G hd hab,
    (uniform_iff_coUniform G hd).mp h.2.1⟩

#print axioms lowBUG_reduction
end Betweenness
```

### `BetweennessCloseOrder.lean`

```lean
import BetweennessReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma weight_pos (h : DiameterTwo G) {a b : Fin n} (hab : Gᶜ.Adj a b) :
    0 < weight Gᶜ a b := by
  unfold weight
  apply one_div_pos.mpr
  exact sub_pos.mpr (by exact_mod_cast pole_lt_of_diameterTwo G h hab)

lemma coBetweenness_lt_of_close_ssubset (h : DiameterTwo G) (x y : Fin n)
    (hs : closeEdges Gᶜ x ⊂ closeEdges Gᶜ y) :
    coBetweenness Gᶜ x < coBetweenness Gᶜ y := by
  obtain ⟨e, he, hne⟩ := Finset.exists_of_ssubset hs
  have hp : ∀ e ∈ closeEdges Gᶜ y, 0 < weight Gᶜ e.1 e.2 := by
    intro e he
    exact weight_pos G h (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2
  exact Finset.sum_lt_sum_of_subset hs.1 he hne (hp e he) (fun e he _ => (hp e he).le)

lemma lowBUG_close_not_ssubset (h : LowBUG G) (x y : Fin n) :
    ¬ closeEdges Gᶜ x ⊂ closeEdges Gᶜ y := by
  intro hs
  have hlt := coBetweenness_lt_of_close_ssubset G (lowBUG_diameterTwo G h) x y hs
  have heq := (lowBUG_reduction G h).2.2.2 x y
  exact (ne_of_lt hlt) heq

#print axioms weight_pos
#print axioms coBetweenness_lt_of_close_ssubset
#print axioms lowBUG_close_not_ssubset
end Betweenness
```

### `BetweennessLeaf.lean`

```lean
import BetweennessCloseOrder

namespace Betweenness
variable {n : ℕ}

lemma close_of_closeEdges_subset (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    {x y a b : Fin n} (hs : closeEdges F y ⊆ closeEdges F x)
    (hab : F.Adj a b) (hy : close F y a b) : close F x a b := by
  rcases lt_or_gt_of_ne hab.ne with hl | hl
  · have he : (a,b) ∈ closeEdges F y := by simp [closeEdges, pairs, hl, hab, hy]
    exact (Finset.mem_filter.mp (hs he)).2
  · have hy' : close F y b a := hy.symm
    have he : (b,a) ∈ closeEdges F y := by simp [closeEdges, pairs, hl, hab.symm, hy']
    exact (Finset.mem_filter.mp (hs he)).2.symm

/-- The leaf argument underlying source Lemma 14, with uniqueness of the
neighbour exposed so no degree convention is hidden. -/
theorem lowBUG_component_of_leaf (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (x y : Fin n)
    (hxK : x ∈ K.supp) (hxy : Gᶜ.Adj x y)
    (hx : ∀ z, Gᶜ.Adj x z → z = y) : ∃ l, StarComponent Gᶜ l K := by
  classical
  have hyK := K.mem_supp_of_adj_mem_supp hxK hxy
  have hsub : closeEdges Gᶜ x ⊆ closeEdges Gᶜ y := by
    intro ab hab
    obtain ⟨he, hc⟩ := Finset.mem_filter.mp hab
    have hadj := (Finset.mem_filter.mp he).2.2
    apply Finset.mem_filter.mpr
    refine ⟨he, ?_⟩
    rcases hc with ha | hb
    · exact Or.inr (hx _ ha ▸ hadj)
    · exact Or.inl (hx _ hb ▸ hadj.symm)
  have heq : closeEdges Gᶜ x = closeEdges Gᶜ y := by
    by_contra hne
    exact lowBUG_close_not_ssubset G h x y (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hstar : ∀ u v, Gᶜ.Adj y u → Gᶜ.Adj u v → u = y ∨ v = y := by
    intro u v hyu huv
    have hclose : close Gᶜ y u v := Or.inl hyu
    have hc := close_of_closeEdges_subset Gᶜ (le_of_eq heq.symm) huv hclose
    exact hc.elim (fun hu => Or.inl (hx _ hu)) (fun hv => Or.inr (hx _ hv))
  have hreach : ∀ v, Gᶜ.Reachable y v → v = y ∨ Gᶜ.Adj y v := by
    intro v hv
    obtain ⟨p⟩ := hv
    have hwalk : ∀ {u v}, (p : Gᶜ.Walk u v) → (u = y ∨ Gᶜ.Adj y u) →
        v = y ∨ Gᶜ.Adj y v := by
      intro u v p
      induction p with
      | nil => exact id
      | @cons u z v huz p ih =>
        intro hu
        apply ih
        rcases hu with rfl | hu
        · exact Or.inr huz
        · rcases hstar u z hu huz with he | he
          · exact (hu.ne he.symm).elim
          · exact Or.inl he
    exact hwalk p (Or.inl rfl)
  have hvertices : ∀ v ∈ K.supp, v = y ∨ Gᶜ.Adj y v := by
    intro v hv
    exact hreach v (K.reachable_of_mem_supp hyK hv)
  have hpos : 0 < K.supp.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact Finset.card_pos.mpr ⟨y, Set.mem_toFinset.mpr hyK⟩
  refine ⟨K.supp.ncard - 1, y, hyK, by omega, ?_⟩
  intro u hu v hv
  constructor
  · intro huv
    refine ⟨huv.ne, ?_⟩
    rcases hvertices u hu with he | hyu
    · exact Or.inl he
    · exact hstar u v hyu huv
  · rintro ⟨huv, he | he⟩
    · subst u
      exact (hvertices v hv).resolve_left (Ne.symm huv)
    · subst v
      exact ((hvertices u hu).resolve_left huv).symm

#print axioms lowBUG_component_of_leaf
end Betweenness
```

### `BetweennessStarExistence.lean`

```lean
import BetweennessLeaf
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma isolated_starComponent (F : SimpleGraph (Fin n)) (K : F.ConnectedComponent)
    (x : Fin n) (hxK : x ∈ K.supp) (hx : F.IsIsolated x) : StarComponent F 0 K := by
  have hs : K.supp = {x} := by
    ext v
    constructor
    · intro hv
      obtain ⟨p⟩ := K.reachable_of_mem_supp hxK hv
      cases p with
      | nil => rfl
      | cons h _ => exact (hx _ h).elim
    · intro hv
      simp only [Set.mem_singleton_iff] at hv
      exact hv ▸ hxK
  refine ⟨x, hxK, ?_, ?_⟩
  · rw [hs, Set.ncard_singleton]
  · rw [hs]
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    subst u; subst v; simp

lemma lowBUG_component_of_degree_le_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (x : Fin n) (hxK : x ∈ K.supp)
    (hx : Gᶜ.degree x ≤ 1) : ∃ l, StarComponent Gᶜ l K := by
  by_cases hz : Gᶜ.degree x = 0
  · exact ⟨0, isolated_starComponent Gᶜ K x hxK ((Gᶜ.degree_eq_zero x).mp hz)⟩
  · have h1 : Gᶜ.degree x = 1 := by omega
    obtain ⟨y, hxy, hy⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h1
    exact lowBUG_component_of_leaf G h K x y hxK hxy hy

lemma lowBUG_exists_degree_le_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) : ∃ x, Gᶜ.degree x ≤ 1 := by
  classical
  by_contra hn
  have hall : ∀ x, 2 ≤ Gᶜ.degree x := by simpa only [not_exists, not_le, Nat.succ_le_iff] using hn
  have hs : ∑ _x : Fin n, 2 ≤ ∑ x, Gᶜ.degree x :=
    Finset.sum_le_sum (fun x _ => hall x)
  rw [Gᶜ.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hsp := lowBUG_sparse G h
  rw [pairs_card_eq_edgeSet, Nat.card_eq_fintype_card, ← Gᶜ.edgeFinset_card] at hsp
  omega

lemma lowBUG_exists_starComponent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) : ∃ l, ∃ K : Gᶜ.ConnectedComponent, StarComponent Gᶜ l K := by
  obtain ⟨x, hx⟩ := lowBUG_exists_degree_le_one G h
  obtain ⟨l, hl⟩ := lowBUG_component_of_degree_le_one G h (Gᶜ.connectedComponentMk x) x
    (by rfl) hx
  exact ⟨l, _, hl⟩

#print axioms lowBUG_component_of_degree_le_one
#print axioms lowBUG_exists_degree_le_one
#print axioms lowBUG_exists_starComponent
end Betweenness
```

### `BetweennessDoubleCount.lean`

```lean
import BetweennessComplement
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace Betweenness
variable {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]

omit [DecidableRel F.Adj] in
lemma close_component_iff (K : F.ConnectedComponent) {x a b : Fin n}
    (hab : F.Adj a b) (hx : close F x a b) : x ∈ K.supp ↔ a ∈ K.supp := by
  rcases hx with hxa | hxb
  · exact K.mem_supp_congr_adj hxa
  · exact (K.mem_supp_congr_adj hxb).trans (K.mem_supp_congr_adj hab).symm

lemma weighted_double_count (K : F.ConnectedComponent) (f : Fin n × Fin n → ℚ) :
    ∑ v ∈ K.supp.toFinset, ∑ e ∈ closeEdges F v, f e =
      ∑ e ∈ componentEdges F K, (pole F e.1 e.2 : ℚ) * f e := by
  classical
  simp only [closeEdges, Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold componentEdges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hadj := (Finset.mem_filter.mp he).2.2
  by_cases hk : e.1 ∈ K.supp
  · have hs : K.supp.toFinset.filter (fun v => close F v e.1 e.2) =
        closeVertices F e.1 e.2 := by
      ext v
      simp only [Finset.mem_filter, Set.mem_toFinset, closeVertices,
        Finset.mem_univ, true_and]
      exact ⟨fun hv => hv.2, fun hv => ⟨(close_component_iff F K hadj hv).mpr hk, hv⟩⟩
    simp only [hk, ite_true]
    rw [← Finset.sum_filter, Finset.sum_const, hs, nsmul_eq_mul]
    rfl
  · have hs : K.supp.toFinset.filter (fun v => close F v e.1 e.2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hv, hc⟩ := Finset.mem_filter.mp hv
      exact hk ((close_component_iff F K hadj hc).mp (Set.mem_toFinset.mp hv))
    simp only [hk, ite_false]
    rw [← Finset.sum_filter, hs, Finset.sum_empty]

lemma close_double_count (K : F.ConnectedComponent) :
    ∑ v ∈ K.supp.toFinset, (closeEdges F v).card =
      ∑ e ∈ componentEdges F K, pole F e.1 e.2 := by
  classical
  have hh := weighted_double_count F K (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  exact_mod_cast hh

lemma co_double_count (K : F.ConnectedComponent) :
    ∑ v ∈ K.supp.toFinset, coBetweenness F v =
      ∑ e ∈ componentEdges F K, (pole F e.1 e.2 : ℚ) * weight F e.1 e.2 := by
  exact weighted_double_count F K (fun e => weight F e.1 e.2)

#print axioms close_double_count
#print axioms co_double_count
end Betweenness
```

### `BetweennessStarValue.lean`

```lean
import BetweennessDoubleCount
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

def orderedPair (a b : Fin n) : Fin n × Fin n := if a < b then (a,b) else (b,a)

lemma star_component_edge_count (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) (l : ℕ) (hs : StarComponent F l K) :
    (componentEdges F K).card = l := by
  classical
  obtain ⟨c, hc, hsize, hform⟩ := hs
  let leaves := K.supp.toFinset.erase c
  have hcard : leaves.card = l := by
    dsimp [leaves]
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hc),
      ← Set.ncard_eq_toFinset_card']
    omega
  have hb : leaves.card = (componentEdges F K).card := by
    apply Finset.card_bij (fun b _ => orderedPair c b)
    · intro b hb
      have hbK : b ∈ K.supp := Set.mem_toFinset.mp (Finset.mem_erase.mp hb).2
      have hbc : b ≠ c := (Finset.mem_erase.mp hb).1
      have hcb : F.Adj c b := (hform c hc b hbK).mpr ⟨Ne.symm hbc, Or.inl rfl⟩
      by_cases hlt : c < b
      · simp only [orderedPair, hlt, ite_true]
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hcb⟩, hc⟩
      · have hlt' : b < c := lt_of_le_of_ne (le_of_not_gt hlt) hbc
        simp only [orderedPair, hlt, ite_false]
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt', hcb.symm⟩, hbK⟩
    · intro b hb d hd he
      have hbc := (Finset.mem_erase.mp hb).1
      have hdc := (Finset.mem_erase.mp hd).1
      by_cases hcb : c < b <;> by_cases hcd : c < d <;>
        simp_all [orderedPair, Prod.mk.injEq]
    · rintro ⟨a,b⟩ hab
      have hab' := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
      have haK := (Finset.mem_filter.mp hab).2
      have hbK := K.mem_supp_of_adj_mem_supp haK hab'.2
      rcases (hform a haK b hbK).mp hab'.2 with ⟨hne, ha | hb⟩
      · subst a
        exact ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hne, Set.mem_toFinset.mpr hbK⟩,
          by simp [orderedPair, hab'.1]⟩
      · subst b
        refine ⟨a, Finset.mem_erase.mpr ⟨hne, Set.mem_toFinset.mpr haK⟩, ?_⟩
        simp [orderedPair, not_lt_of_gt hab'.1]
  omega

lemma star_edge_closeVertices (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) (l : ℕ) (hs : StarComponent F l K)
    {a b : Fin n} (he : (a,b) ∈ componentEdges F K) :
    closeVertices F a b = K.supp.toFinset := by
  classical
  obtain ⟨c, hc, _, hform⟩ := hs
  have hadj := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2
  have haK := (Finset.mem_filter.mp he).2
  have hbK := K.mem_supp_of_adj_mem_supp haK hadj
  have hcent := ((hform a haK b hbK).mp hadj).2
  ext x
  simp only [closeVertices, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  constructor
  · intro hx
    exact (close_component_iff F K hadj hx).mpr haK
  · intro hxK
    by_cases hxc : x = c
    · subst x
      rcases hcent with rfl | rfl
      · exact Or.inr hadj
      · exact Or.inl hadj.symm
    · have hxc' : F.Adj x c := (hform x hxK c hc).mpr ⟨hxc, Or.inr rfl⟩
      exact hcent.elim (fun ha => Or.inl (ha ▸ hxc')) (fun hb => Or.inr (hb ▸ hxc'))

lemma star_closeEdges (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) (l : ℕ) (hs : StarComponent F l K)
    (v : Fin n) (hv : v ∈ K.supp) : closeEdges F v = componentEdges F K := by
  classical
  ext ab
  constructor
  · intro hab
    obtain ⟨he, hc⟩ := Finset.mem_filter.mp hab
    have hadj := (Finset.mem_filter.mp he).2.2
    exact Finset.mem_filter.mpr ⟨he, (close_component_iff F K hadj hc).mp hv⟩
  · intro hab
    have hc : v ∈ closeVertices F ab.1 ab.2 := by
      rw [star_edge_closeVertices F K l hs hab]
      exact Set.mem_toFinset.mpr hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).1, (Finset.mem_filter.mp hc).2⟩

lemma star_coBetweenness (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) (l : ℕ) (hs : StarComponent F l K)
    (v : Fin n) (hv : v ∈ K.supp) :
    coBetweenness F v = (l : ℚ) / ((n : ℚ) - l - 1) := by
  classical
  unfold coBetweenness
  rw [star_closeEdges F K l hs v hv]
  have hp : ∀ ab ∈ componentEdges F K, pole F ab.1 ab.2 = l + 1 := by
    intro ab hab
    unfold pole
    rw [star_edge_closeVertices F K l hs hab, ← Set.ncard_eq_toFinset_card']
    exact hs.choose_spec.2.1
  have hw : ∀ ab ∈ componentEdges F K, weight F ab.1 ab.2 =
      1 / ((n : ℚ) - l - 1) := by
    intro ab hab
    unfold weight
    rw [hp ab hab, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul,
    star_component_edge_count F K l hs]
  simp [div_eq_mul_inv]

#print axioms star_component_edge_count
#print axioms star_closeEdges
#print axioms star_coBetweenness
end Betweenness
```

### `BetweennessStarReduction.lean`

```lean
import BetweennessStarExistence
import BetweennessStarValue
import Mathlib.Tactic.FieldSimp

namespace Betweenness
variable {n : ℕ}

lemma component_ncard_le (F : SimpleGraph (Fin n)) (K : F.ConnectedComponent) :
    K.supp.ncard ≤ n := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  exact (Finset.card_le_univ K.supp.toFinset).trans_eq (Fintype.card_fin n)

lemma star_size_lt_of_lowBUG (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (l : ℕ)
    (hs : StarComponent Gᶜ l K) (hn : 1 < n) : l + 1 < n := by
  classical
  by_cases hl : l = 0
  · simpa [hl] using hn
  have he : (componentEdges Gᶜ K).Nonempty := by
    apply Finset.card_pos.mp
    rw [star_component_edge_count Gᶜ K l hs]
    omega
  obtain ⟨ab, hab⟩ := he
  have hp : pole Gᶜ ab.1 ab.2 = l + 1 := by
    unfold pole
    rw [star_edge_closeVertices Gᶜ K l hs hab, ← Set.ncard_eq_toFinset_card']
    exact hs.choose_spec.2.1
  have hd := pole_lt_of_diameterTwo G (lowBUG_diameterTwo G h)
    (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2.2
  omega

lemma lowBUG_star_sizes_equal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K L : Gᶜ.ConnectedComponent) (l k : ℕ)
    (hs : StarComponent Gᶜ l K) (ht : StarComponent Gᶜ k L) : l = k := by
  have hln : l + 1 ≤ n := by
    rw [← hs.choose_spec.2.1]
    exact component_ncard_le Gᶜ K
  have hkn : k + 1 ≤ n := by
    rw [← ht.choose_spec.2.1]
    exact component_ncard_le Gᶜ L
  by_cases hn : 1 < n
  · have hl' := star_size_lt_of_lowBUG G h K l hs hn
    have hk' := star_size_lt_of_lowBUG G h L k ht hn
    have hlq : (l : ℚ) + 1 < n := by exact_mod_cast hl'
    have hkq : (k : ℚ) + 1 < n := by exact_mod_cast hk'
    have hd1 : (n : ℚ) - l - 1 ≠ 0 := ne_of_gt (by linarith)
    have hd2 : (n : ℚ) - k - 1 ≠ 0 := ne_of_gt (by linarith)
    have heq := (lowBUG_reduction G h).2.2.2 hs.choose ht.choose
    rw [star_coBetweenness Gᶜ K l hs hs.choose hs.choose_spec.1,
      star_coBetweenness Gᶜ L k ht ht.choose ht.choose_spec.1] at heq
    have hh := (div_eq_div_iff hd1 hd2).mp heq
    have hz : ((l : ℚ) - k) * ((n : ℚ) - 1) = 0 := by nlinarith [hh]
    have hnq : (1 : ℚ) < n := by exact_mod_cast hn
    have hn' : (n : ℚ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hlk := (mul_eq_zero.mp hz).resolve_right hn'
    exact_mod_cast (sub_eq_zero.mp hlk)
  · omega

lemma star_component_reduction (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) :
    ∃ l, (∃ K, StarComponent Gᶜ l K) ∧
      (∀ K k, StarComponent Gᶜ k K → k = l) ∧
      (∀ K, (∃ v ∈ K.supp, Gᶜ.degree v ≤ 1) → StarComponent Gᶜ l K) := by
  obtain ⟨l, K, hs⟩ := lowBUG_exists_starComponent G h
  have heq : ∀ J k, StarComponent Gᶜ k J → k = l := by
    intro J k hk
    exact lowBUG_star_sizes_equal G h J K k l hk hs
  refine ⟨l, ⟨K, hs⟩, heq, ?_⟩
  intro J hJ
  obtain ⟨v, hv, hd⟩ := hJ
  obtain ⟨k, hk⟩ := lowBUG_component_of_degree_le_one G h J v hv hd
  exact heq J k hk ▸ hk

#print axioms lowBUG_star_sizes_equal
#print axioms star_component_reduction
end Betweenness
```

### `BetweennessComponentCounts.lean`

```lean
import BetweennessStarReduction

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

def componentGraph (F : SimpleGraph (Fin n)) (K : F.ConnectedComponent) : SimpleGraph (Fin n) where
  Adj u v := F.Adj u v ∧ u ∈ K.supp
  symm := ⟨by intro u v h; exact ⟨h.1.symm, K.mem_supp_of_adj_mem_supp h.2 h.1⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

lemma pairs_componentGraph (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) :
    (by classical exact pairs (componentGraph F K)) = componentEdges F K := by
  classical
  ext ab
  simp [pairs, componentEdges, componentGraph, and_assoc]

lemma component_degree_sum (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) :
    ∑ v ∈ K.supp.toFinset, F.degree v = 2 * (componentEdges F K).card := by
  classical
  let H := componentGraph F K
  have hi : ∀ v ∈ K.supp, H.degree v = F.degree v := by
    intro v hv
    change (H.neighborFinset v).card = (F.neighborFinset v).card
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact and_iff_left hv
  have ho : ∀ v ∉ K.supp, H.degree v = 0 := by
    intro v hv
    apply (H.degree_eq_zero v).mpr
    intro w hw
    exact hv hw.2
  have he : H.edgeFinset.card = (componentEdges F K).card := by
    rw [← pairs_componentGraph F K]
    rw [pairs_card_eq_edgeSet, Nat.card_eq_fintype_card, H.card_edgeSet]
  have hs := H.sum_degrees_eq_twice_card_edges
  rw [he] at hs
  rw [← hs]
  have hset : K.supp.toFinset = Finset.univ.filter (fun v => v ∈ K.supp) := by
    ext v; simp
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hk : v ∈ K.supp
  · simp only [hk, ite_true]
    exact (hi v hk).symm
  · simp only [hk, ite_false]
    exact (ho v hk).symm

lemma component_vertices_sum (F : SimpleGraph (Fin n)) [Fintype F.ConnectedComponent] :
    ∑ K : F.ConnectedComponent, K.supp.ncard = n := by
  classical
  simp_rw [Set.ncard_eq_toFinset_card']
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset F.ConnectedComponent) F.connectedComponentMk
  have hset : ∀ K : F.ConnectedComponent,
      (Finset.univ.filter (fun v => F.connectedComponentMk v = K)) = K.supp.toFinset := by
    intro K; ext v; simp
  simp_rw [hset] at hh
  simpa using hh

lemma component_edges_sum (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    [Fintype F.ConnectedComponent] :
    ∑ K : F.ConnectedComponent, (componentEdges F K).card = (pairs F).card := by
  classical
  have hh := Finset.sum_card_fiberwise_eq_card_filter (pairs F)
    (Finset.univ : Finset F.ConnectedComponent) (fun e => F.connectedComponentMk e.1)
  simpa only [componentEdges, SimpleGraph.ConnectedComponent.mem_supp_iff,
    Finset.mem_univ, Finset.filter_true] using hh

lemma nonstar_component_edges_ge_vertices (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K) :
    K.supp.ncard ≤ (componentEdges Gᶜ K).card := by
  classical
  have hd : ∀ v ∈ K.supp, 2 ≤ Gᶜ.degree v := by
    intro v hv
    by_contra hc
    exact hk (lowBUG_component_of_degree_le_one G h K v hv (by omega))
  have hs : ∑ _v ∈ K.supp.toFinset, 2 ≤ ∑ v ∈ K.supp.toFinset, Gᶜ.degree v :=
    Finset.sum_le_sum (fun v hv => hd v (Set.mem_toFinset.mp hv))
  rw [component_degree_sum] at hs
  have hcard : K.supp.toFinset.card = K.supp.ncard := (Set.ncard_eq_toFinset_card' _).symm
  simp only [Finset.sum_const, smul_eq_mul, hcard] at hs
  omega

#print axioms component_degree_sum
#print axioms component_vertices_sum
#print axioms component_edges_sum
#print axioms nonstar_component_edges_ge_vertices
end Betweenness
```

### `BetweennessExcess.lean`

```lean
import BetweennessComponentCounts

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma exotic_star_count (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent)
    (hk : ¬ ∃ k, StarComponent Gᶜ k K)
    (l : ℕ) (hs : ∃ J, StarComponent Gᶜ l J) :
    K.supp.ncard + ((componentEdges Gᶜ K).card - K.supp.ncard + 1) * (l + 1) ≤ n := by
  classical
  let _ := Fintype.ofFinite Gᶜ.ConnectedComponent
  let U : Finset Gᶜ.ConnectedComponent := Finset.univ
  let S := U.filter (fun J => ∃ k, StarComponent Gᶜ k J)
  let T := Sᶜ
  have hK : K ∈ T := by simpa only [T, S, U, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  have hJ : ∀ J ∈ S, StarComponent Gᶜ l J := by
    intro J hJ
    obtain ⟨k, hj⟩ := (Finset.mem_filter.mp hJ).2
    obtain ⟨L, hL⟩ := hs
    have he := lowBUG_star_sizes_equal G h J L k l hj hL
    exact he ▸ hj
  have hsV : ∑ J ∈ S, J.supp.ncard = S.card * (l + 1) := by
    calc
      _ = ∑ _J ∈ S, (l + 1) := Finset.sum_congr rfl (fun J hj => (hJ J hj).choose_spec.2.1)
      _ = _ := by simp
  have hsE : ∑ J ∈ S, (componentEdges Gᶜ J).card = S.card * l := by
    calc
      _ = ∑ _J ∈ S, l := Finset.sum_congr rfl (fun J hj => star_component_edge_count Gᶜ J l (hJ J hj))
      _ = _ := by simp
  have hT : ∀ J ∈ T, J.supp.ncard ≤ (componentEdges Gᶜ J).card := by
    intro J hj
    apply nonstar_component_edges_ge_vertices G h J
    simpa [T, S, U] using hj
  have hV : S.card * (l + 1) + ∑ J ∈ T, J.supp.ncard = n := by
    rw [← hsV]
    have hh := Finset.sum_add_sum_compl S (fun J => J.supp.ncard)
    have he : (∑ J ∈ S, J.supp.ncard) + (∑ J ∈ T, J.supp.ncard) =
        ∑ J : Gᶜ.ConnectedComponent, J.supp.ncard := by simpa [T, U] using hh
    rw [he, component_vertices_sum]
  have hE : S.card * l + ∑ J ∈ T, (componentEdges Gᶜ J).card < n := by
    rw [← hsE]
    have hh := Finset.sum_add_sum_compl S (fun J => (componentEdges Gᶜ J).card)
    have he : (∑ J ∈ S, (componentEdges Gᶜ J).card) + (∑ J ∈ T, (componentEdges Gᶜ J).card) =
        ∑ J : Gᶜ.ConnectedComponent, (componentEdges Gᶜ J).card := by simpa [T, U] using hh
    rw [he, component_edges_sum]
    exact lowBUG_sparse G h
  have hrest := Finset.sum_le_sum (s := T.erase K) (fun J hj => hT J (Finset.mem_of_mem_erase hj))
  have hvK : K.supp.ncard ≤ ∑ J ∈ T, J.supp.ncard :=
    Finset.single_le_sum (f := fun J : Gᶜ.ConnectedComponent => J.supp.ncard) (fun _ _ => Nat.zero_le _) hK
  have hvsplit := Finset.sum_erase_add T (fun J => J.supp.ncard) hK
  have hesplit := Finset.sum_erase_add T (fun J => (componentEdges Gᶜ J).card) hK
  have hm := hT K hK
  have hS : (componentEdges Gᶜ K).card - K.supp.ncard + 1 ≤ S.card := by
    simp only [Nat.mul_add, Nat.mul_one] at hV
    omega
  have hmul := Nat.mul_le_mul_right (l + 1) hS
  nlinarith

#print axioms exotic_star_count
end Betweenness
```

### `BetweennessUniformComponent.lean`

```lean
import BetweennessExcess

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma uniform_component_impossible (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent)
    (hk : ¬ ∃ k, StarComponent Gᶜ k K)
    (hc : ∀ v ∈ K.supp, closeEdges Gᶜ v = componentEdges Gᶜ K)
    (hp : ∀ ab ∈ componentEdges Gᶜ K, pole Gᶜ ab.1 ab.2 = K.supp.ncard) : False := by
  classical
  obtain ⟨l, J, hs⟩ := lowBUG_exists_starComponent G h
  have ht : 0 < K.supp.ncard := by
    rw [Set.ncard_pos (Set.toFinite _)]
    exact K.nonempty_supp
  have hm := nonstar_component_edges_ge_vertices G h K hk
  have hlo := exotic_star_count G h K hk l ⟨J, hs⟩
  have hln : l + 1 < n := star_size_lt_of_lowBUG G h J l hs (by nlinarith)
  have htn : K.supp.ncard < n := by nlinarith
  obtain ⟨v, hv⟩ := K.nonempty_supp
  have hq := (lowBUG_reduction G h).2.2.2 v hs.choose
  rw [star_coBetweenness Gᶜ J l hs hs.choose hs.choose_spec.1] at hq
  have hval : coBetweenness Gᶜ v =
      ((componentEdges Gᶜ K).card : ℚ) / ((n : ℚ) - K.supp.ncard) := by
    unfold coBetweenness
    rw [hc v hv]
    simp_rw [weight]
    have : ∀ ab ∈ componentEdges Gᶜ K,
        1 / ((n : ℚ) - pole Gᶜ ab.1 ab.2) = 1 / ((n : ℚ) - K.supp.ncard) := by
      intro ab hab; rw [hp ab hab]
    rw [Finset.sum_congr rfl this]
    simp [div_eq_mul_inv]
  rw [hval] at hq
  have htnq : (K.supp.ncard : ℚ) < n := by exact_mod_cast htn
  have hlnq : (l : ℚ) + 1 < n := by exact_mod_cast hln
  have heq := (div_eq_div_iff (by linarith : (n : ℚ) - K.supp.ncard ≠ 0)
    (by linarith : (n : ℚ) - l - 1 ≠ 0)).mp hq
  have hmq : (K.supp.ncard : ℚ) ≤ (componentEdges Gᶜ K).card := by exact_mod_cast hm
  have htq : (0 : ℚ) < K.supp.ncard := by exact_mod_cast ht
  have hlm : l < (componentEdges Gᶜ K).card := by
    by_contra hh
    have hhq : ((componentEdges Gᶜ K).card : ℚ) ≤ l := by exact_mod_cast (Nat.le_of_not_gt hh)
    have hnon : (0 : ℚ) ≤ l * ((componentEdges Gᶜ K).card - K.supp.ncard) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmq)
    nlinarith
  have hlmq : (l : ℚ) + 1 ≤ (componentEdges Gᶜ K).card := by exact_mod_cast hlm
  have hd : ((componentEdges Gᶜ K).card : ℚ) - K.supp.ncard =
      ((componentEdges Gᶜ K).card - K.supp.ncard : ℕ) := by rw [Nat.cast_sub hm]
  have hloq : (K.supp.ncard : ℚ) +
      (((componentEdges Gᶜ K).card - K.supp.ncard : ℕ) + 1) * ((l : ℚ) + 1) ≤ n := by
    exact_mod_cast hlo
  nlinarith

#print axioms uniform_component_impossible
end Betweenness
```

### `BetweennessTriangle.lean`

```lean
import BetweennessUniformComponent

namespace Betweenness
variable {n : ℕ}

lemma closeEdges_eq_of_subset (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) {x y : Fin n} (hs : closeEdges Gᶜ x ⊆ closeEdges Gᶜ y) :
    closeEdges Gᶜ x = closeEdges Gᶜ y := by
  by_contra hn
  exact lowBUG_close_not_ssubset G h x y (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hn⟩)

lemma exotic_no_degree_two_triangle (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    (a b c : Fin n) (ha : a ∈ K.supp)
    (hab : Gᶜ.Adj a b) (hbc : Gᶜ.Adj b c) (hca : Gᶜ.Adj c a) :
    Gᶜ.degree a ≠ 2 := by
  classical
  intro hdeg
  have hb := K.mem_supp_of_adj_mem_supp ha hab
  have hc := K.mem_supp_of_adj_mem_supp ha hca.symm
  have hneigh : ∀ z, Gᶜ.Adj a z → z = b ∨ z = c := by
    have hset : Gᶜ.neighborFinset a = {b,c} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [hab, hca.symm]
      · simp [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hbc.ne]
    intro z hz
    have hh : z ∈ Gᶜ.neighborFinset a := by simpa using hz
    simpa [hset] using hh
  have hsub (y z : Fin n) (hay : Gᶜ.Adj a y) (haz : Gᶜ.Adj a z)
      (hyz : Gᶜ.Adj y z) (hn : ∀ w, Gᶜ.Adj a w → w = y ∨ w = z) :
      closeEdges Gᶜ a ⊆ closeEdges Gᶜ y := by
    intro uv huv
    obtain ⟨he, hx⟩ := Finset.mem_filter.mp huv
    have huv' := (Finset.mem_filter.mp he).2.2
    refine Finset.mem_filter.mpr ⟨he, ?_⟩
    rcases hx with hx | hx
    · rcases hn _ hx with hu | hu
      · exact Or.inr (hu ▸ huv')
      · exact Or.inl (hu ▸ hyz)
    · rcases hn _ hx with hv | hv
      · exact Or.inl (hv ▸ huv'.symm)
      · exact Or.inr (hv ▸ hyz)
  have heb := closeEdges_eq_of_subset G h (hsub b c hab hca.symm hbc hneigh)
  have hec := closeEdges_eq_of_subset G h (hsub c b hca.symm hab hbc.symm
    (fun z hz => (hneigh z hz).symm))
  have htouch (y : Fin n) (hy : y = b ∨ y = c) {u v : Fin n}
      (hyu : Gᶜ.Adj y u) (huv : Gᶜ.Adj u v) :
      u = b ∨ u = c ∨ v = b ∨ v = c := by
    have heq : closeEdges Gᶜ y = closeEdges Gᶜ a := by
      rcases hy with rfl | rfl; exact heb.symm; exact hec.symm
    have hh := close_of_closeEdges_subset Gᶜ (le_of_eq heq) huv (Or.inl hyu)
    rcases hh with hh | hh
    · exact (hneigh _ hh).elim Or.inl (fun hh => Or.inr (Or.inl hh))
    · exact (hneigh _ hh).elim (fun hh => Or.inr (Or.inr (Or.inl hh)))
        (fun hh => Or.inr (Or.inr (Or.inr hh)))
  have hreach : ∀ v, Gᶜ.Reachable b v →
      v = b ∨ v = c ∨ (Gᶜ.Adj b v ∧ Gᶜ.Adj c v) := by
    intro v hv
    obtain ⟨p⟩ := hv
    have hw : ∀ {u v}, (p : Gᶜ.Walk u v) →
        (u = b ∨ u = c ∨ (Gᶜ.Adj b u ∧ Gᶜ.Adj c u)) →
        v = b ∨ v = c ∨ (Gᶜ.Adj b v ∧ Gᶜ.Adj c v) := by
      intro u v p
      induction p with
      | nil => exact id
      | @cons u w v huw p ih =>
        intro hu
        apply ih
        by_cases hwb : w = b
        · exact Or.inl hwb
        by_cases hwc : w = c
        · exact Or.inr (Or.inl hwc)
        have hu' : u = b ∨ u = c := by
          rcases hu with hh | hh | hh
          · exact Or.inl hh
          · exact Or.inr hh
          · rcases htouch b (Or.inl rfl) hh.1 huw with he | he | he | he
            · exact (hh.1.ne he.symm).elim
            · exact Or.inr he
            · exact (hwb he).elim
            · exact (hwc he).elim
        have hwK : w ∈ K.supp := by
          apply K.mem_supp_of_adj_mem_supp ?_ huw
          rcases hu' with rfl | rfl
          · exact hb
          · exact hc
        have hdegree : 2 ≤ Gᶜ.degree w := by
          by_contra hh
          exact hk (lowBUG_component_of_degree_le_one G h K w hwK (by omega))
        have hends : ∀ z, Gᶜ.Adj w z → z = b ∨ z = c := by
          intro z hwz
          rcases htouch u hu' huw hwz with hh | hh | hh | hh
          · exact (hwb hh).elim
          · exact (hwc hh).elim
          · exact Or.inl hh
          · exact Or.inr hh
        have hset : Gᶜ.neighborFinset w = {b,c} := by
          apply Finset.eq_of_subset_of_card_le
          · intro z hz; simpa using hends z (by simpa using hz)
          · simpa [hbc.ne, SimpleGraph.card_neighborFinset_eq_degree] using hdegree
        have hbw : Gᶜ.Adj w b := by
          have hh : b ∈ Gᶜ.neighborFinset w := by simp [hset]
          simpa using hh
        have hcw : Gᶜ.Adj w c := by
          have hh : c ∈ Gᶜ.neighborFinset w := by simp [hset]
          simpa using hh
        exact Or.inr (Or.inr ⟨hbw.symm, hcw.symm⟩)
    exact hw p (Or.inl rfl)
  have hverts : ∀ v ∈ K.supp, v = b ∨ v = c ∨ (Gᶜ.Adj b v ∧ Gᶜ.Adj c v) :=
    fun v hv => hreach v (K.reachable_of_mem_supp hb hv)
  have hedges : ∀ {u v}, Gᶜ.Adj u v → u ∈ K.supp →
      u = b ∨ u = c ∨ v = b ∨ v = c := by
    intro u v huv hu
    rcases hverts u hu with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact htouch b (Or.inl rfl) hh.1 huv
  have hclose : ∀ v ∈ K.supp, ∀ u ∈ K.supp, ∀ w, Gᶜ.Adj u w → close Gᶜ v u w := by
    intro v hv u hu w huw
    rcases hedges huw hu with rfl | rfl | rfl | rfl
    all_goals
      rcases hverts v hv with rfl | rfl | hh <;>
        simp_all [close, SimpleGraph.adj_comm]
  apply uniform_component_impossible G h K hk
  · intro v hv
    ext uv
    simp only [closeEdges, componentEdges, Finset.mem_filter]
    constructor
    · intro he
      exact ⟨he.1, (close_component_iff Gᶜ K (Finset.mem_filter.mp he.1).2.2 he.2).mp hv⟩
    · intro he
      exact ⟨he.1, hclose v hv uv.1 he.2 uv.2 (Finset.mem_filter.mp he.1).2.2⟩
  · intro uv he
    have he' := Finset.mem_filter.mp he
    have hadj := (Finset.mem_filter.mp he'.1).2.2
    have hset : closeVertices Gᶜ uv.1 uv.2 = K.supp.toFinset := by
      ext v
      simp only [closeVertices, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
      constructor
      · intro hv
        exact (close_component_iff Gᶜ K hadj hv).mpr he'.2
      · intro hv
        exact hclose v hv uv.1 he'.2 uv.2 hadj
    simpa [pole, hset] using (Set.ncard_eq_toFinset_card' K.supp).symm

#print axioms exotic_no_degree_two_triangle
end Betweenness
```

### `BetweennessIncidence.lean`

```lean
import BetweennessComponentCounts

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma pairs_incident_sum (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (u : Fin n) (f : Fin n → ℕ) :
    ∑ ab ∈ pairs F, ((if ab.1 = u then f ab.2 else 0) +
      (if ab.2 = u then f ab.1 else 0)) = ∑ w ∈ F.neighborFinset u, f w := by
  classical
  rw [Finset.sum_add_distrib]
  have hleft : (∑ ab ∈ pairs F, if ab.1 = u then f ab.2 else 0) =
      ∑ w, if u < w ∧ F.Adj u w then f w else 0 := by
    simp only [pairs, Finset.sum_filter, Fintype.sum_prod_type]
    have hh : ∀ x w : Fin n,
        (if x < w ∧ F.Adj x w then if x = u then f w else 0 else 0) =
        (if x = u then if x < w ∧ F.Adj x w then f w else 0 else 0) := by
      intro x w; split_ifs <;> rfl
    simp_rw [hh, Finset.sum_ite_irrel]
    simp
  have hright : (∑ ab ∈ pairs F, if ab.2 = u then f ab.1 else 0) =
      ∑ w, if w < u ∧ F.Adj u w then f w else 0 := by
    simp only [pairs, Finset.sum_filter, Fintype.sum_prod_type]
    have hh : ∀ x w : Fin n,
        (if x < w ∧ F.Adj x w then if w = u then f x else 0 else 0) =
        (if w = u then if x < w ∧ F.Adj x w then f x else 0 else 0) := by
      intro x w; split_ifs <;> rfl
    simp_rw [hh]
    simp [SimpleGraph.adj_comm]
  rw [hleft, hright, ← Finset.sum_add_distrib]
  rw [show F.neighborFinset u = Finset.univ.filter (F.Adj u) by ext w; simp]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ha : F.Adj u w
  · rcases lt_or_gt_of_ne ha.ne with hh | hh
    · simp [ha, hh, not_lt_of_ge hh.le]
    · simp [ha, hh, not_lt_of_ge hh.le]
  · simp [ha]

lemma close_incidence_double (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (v : Fin n) :
    ∑ u ∈ F.neighborFinset v, ∑ w ∈ F.neighborFinset u,
      (if F.Adj v w then 1 else 2) = 2 * (closeEdges F v).card := by
  classical
  simp_rw [← pairs_incident_sum F _ (fun w => if F.Adj v w then 1 else 2)]
  rw [Finset.sum_comm]
  have hterm : ∀ ab ∈ pairs F,
      (∑ u ∈ F.neighborFinset v,
        ((if ab.1 = u then (if F.Adj v ab.2 then 1 else 2) else 0) +
        (if ab.2 = u then (if F.Adj v ab.1 then 1 else 2) else 0))) =
        if close F v ab.1 ab.2 then 2 else 0 := by
    intro ab hab
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, SimpleGraph.mem_neighborFinset]
    by_cases ha : F.Adj v ab.1 <;> by_cases hb : F.Adj v ab.2 <;> simp [ha, hb, close]
  rw [Finset.sum_congr rfl hterm]
  rw [closeEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> rfl

#print axioms pairs_incident_sum
#print axioms close_incidence_double
end Betweenness
```

### `BetweennessLocal.lean`

```lean
import BetweennessTriangle
import BetweennessIncidence

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma exotic_min_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    (v : Fin n) (hv : v ∈ K.supp) : 2 ≤ Gᶜ.degree v := by
  by_contra hh
  exact hk (lowBUG_component_of_degree_le_one G h K v hv (by omega))

lemma exotic_degree_close (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    (v : Fin n) (hv : v ∈ K.supp) : 2 * Gᶜ.degree v ≤ (closeEdges Gᶜ v).card := by
  classical
  have hsum : ∀ u ∈ Gᶜ.neighborFinset v,
      4 ≤ ∑ w ∈ Gᶜ.neighborFinset u, (if Gᶜ.Adj v w then 1 else 2) := by
    intro u hu
    have hvu : Gᶜ.Adj v u := by simpa using hu
    have huK := K.mem_supp_of_adj_mem_supp hv hvu
    have hd := exotic_min_degree G h K hk u huK
    by_cases htwo : Gᶜ.degree u = 2
    · have hnot : ∀ w ∈ Gᶜ.neighborFinset u, ¬ Gᶜ.Adj v w := by
        intro w hw hvw
        have huw : Gᶜ.Adj u w := by simpa using hw
        exact exotic_no_degree_two_triangle G h K hk u v w huK hvu.symm hvw huw.symm htwo
      have heq : (∑ w ∈ Gᶜ.neighborFinset u, (if Gᶜ.Adj v w then 1 else 2)) =
          ∑ _w ∈ Gᶜ.neighborFinset u, 2 := by
        apply Finset.sum_congr rfl
        intro w hw
        simp only [hnot w hw, ite_false]
      rw [heq]
      simp [SimpleGraph.card_neighborFinset_eq_degree, htwo]
    · have hvN : v ∈ Gᶜ.neighborFinset u := by simpa using hvu.symm
      have hs := Finset.sum_erase_add (Gᶜ.neighborFinset u)
        (fun w => if Gᶜ.Adj v w then 1 else 2) hvN
      have hlo : ((Gᶜ.neighborFinset u).erase v).card ≤
          ∑ w ∈ (Gᶜ.neighborFinset u).erase v, (if Gᶜ.Adj v w then 1 else 2) := by
        calc
          _ = ∑ _w ∈ (Gᶜ.neighborFinset u).erase v, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      have hcard := Finset.card_erase_add_one hvN
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
      simp only [SimpleGraph.irrefl, ite_false] at hs
      omega
  have hh := Finset.sum_le_sum hsum
  rw [close_incidence_double] at hh
  simp only [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hh
  omega

lemma exotic_pole_four (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    {a b : Fin n} (ha : a ∈ K.supp) (hab : Gᶜ.Adj a b) : 4 ≤ pole Gᶜ a b := by
  classical
  have hb := K.mem_supp_of_adj_mem_supp ha hab
  have hda := exotic_min_degree G h K hk a ha
  have hdb := exotic_min_degree G h K hk b hb
  have hsub : Gᶜ.neighborFinset a ⊆ closeVertices Gᶜ a b := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by simpa using ((Gᶜ.mem_neighborFinset a z).mp hz).symm)⟩
  have haC : a ∈ closeVertices Gᶜ a b :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hab⟩
  have haN : a ∉ Gᶜ.neighborFinset a := by simp
  have hbound : Gᶜ.degree a + 1 ≤ pole Gᶜ a b := by
    have hh := Finset.card_le_card (Finset.insert_subset haC hsub)
    simpa [Finset.card_insert_of_notMem haN, SimpleGraph.card_neighborFinset_eq_degree, pole] using hh
  by_contra hh
  have htwo : Gᶜ.degree a = 2 := by omega
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne (by change 1 < Gᶜ.degree a; omega) b
  have hac : Gᶜ.Adj a c := by simpa using hc
  obtain ⟨d, hd, hda'⟩ := Finset.exists_mem_ne (by change 1 < Gᶜ.degree b; omega) a
  have hbd : Gᶜ.Adj b d := by simpa using hd
  have hcd : c ≠ d := by
    intro he
    subst d
    exact exotic_no_degree_two_triangle G h K hk a b c ha hab hbd hac.symm htwo
  have hset : ({a,b,c,d} : Finset (Fin n)) ⊆ closeVertices Gᶜ a b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact haC
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hab.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hac.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hbd.symm⟩
  have hcard := Finset.card_le_card hset
  have hfour : ({a,b,c,d} : Finset (Fin n)).card = 4 := by
    simp [hab.ne, hac.ne, hbd.ne, hda'.symm, hcb.symm, hcd]
  rw [hfour] at hcard
  exact hh hcard

lemma exotic_local_bounds (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K) :
    (∀ v ∈ K.supp, 2 * Gᶜ.degree v ≤ (closeEdges Gᶜ v).card) ∧
      (∀ e ∈ pairs Gᶜ, e.1 ∈ K.supp → 4 ≤ pole Gᶜ e.1 e.2) := by
  refine ⟨exotic_degree_close G h K hk, ?_⟩
  intro e he hv
  exact exotic_pole_four G h K hk hv (Finset.mem_filter.mp he).2.2

#print axioms exotic_local_bounds
end Betweenness
```

### `BetweennessEdgeBounds.lean`

```lean
import BetweennessComponentCounts
import Mathlib.Data.Finset.Max

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma closeEdges_subset_component (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K : F.ConnectedComponent) {v : Fin n} (hv : v ∈ K.supp) :
    closeEdges F v ⊆ componentEdges F K := by
  classical
  intro e he
  obtain ⟨he, hc⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨he,
    (close_component_iff F K (Finset.mem_filter.mp he).2.2 hc).mp hv⟩

lemma pole_le_degree_sum (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (a b : Fin n) :
    pole F a b ≤ F.degree a + F.degree b := by
  have hs : closeVertices F a b = F.neighborFinset a ∪ F.neighborFinset b := by
    ext v
    simp [closeVertices, close, F.adj_comm]
  unfold pole
  rw [hs]
  exact Finset.card_union_le _ _

lemma edge_degree_excess_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    {a b : Fin n} (ha : a ∈ K.supp) (hab : Gᶜ.Adj a b) :
    Gᶜ.degree a + Gᶜ.degree b ≤
      2 * ((componentEdges Gᶜ K).card - K.supp.ncard) + 4 := by
  classical
  let V := K.supp.toFinset
  have ha' : a ∈ V := Set.mem_toFinset.mpr ha
  have hb : b ∈ K.supp := K.mem_supp_of_adj_mem_supp ha hab
  have hb' : b ∈ V.erase a := Finset.mem_erase.mpr ⟨hab.ne.symm, Set.mem_toFinset.mpr hb⟩
  have hd : ∀ v ∈ V, 2 ≤ Gᶜ.degree v := by
    intro v hv
    by_contra hh
    exact hk (lowBUG_component_of_degree_le_one G h K v (Set.mem_toFinset.mp hv) (by omega))
  have hh := Finset.sum_le_sum (s := (V.erase a).erase b)
    (fun v hv => hd v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)))
  have hs1 := Finset.sum_erase_add V (fun v => Gᶜ.degree v) ha'
  have hs2 := Finset.sum_erase_add (V.erase a) (fun v => Gᶜ.degree v) hb'
  have hc1 := Finset.card_erase_add_one ha'
  have hc2 := Finset.card_erase_add_one hb'
  have hs : (∑ v ∈ V, Gᶜ.degree v) = 2 * (componentEdges Gᶜ K).card :=
    component_degree_sum Gᶜ K
  have hc : V.card = K.supp.ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hm := nonstar_component_edges_ge_vertices G h K hk
  simp only [Finset.sum_const, smul_eq_mul] at hh
  omega

lemma adjacent_close_pair (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    {v u : Fin n} (hvu : F.Adj v u) :
    ∃ e ∈ closeEdges F v,
      (e.1 = v ∧ e.2 = u) ∨ (e.1 = u ∧ e.2 = v) := by
  rcases lt_or_gt_of_ne hvu.ne with hh | hh
  · refine ⟨(v,u), ?_, Or.inl ⟨rfl,rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hvu⟩, Or.inr hvu⟩
  · refine ⟨(u,v), ?_, Or.inr ⟨rfl,rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hvu.symm⟩, Or.inl hvu⟩

#print axioms edge_degree_excess_bound
end Betweenness
```

### `GraphNumericalCore.lean`

```lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace LowBUG

/-- The degree/excess and maximum-closeness bounds cannot both hold
when a vertex has too few close edges and the maximum exceeds ell+1. -/
theorem small_vertex_bounds_impossible
    (ell e t n : ℚ) (hl : 4 ≤ ell) (ht : 1 ≤ t)
    (he : ell - 3 ≤ 2 * e)
    (hlo : (e + 1) * (ell + 1) + t ≤ n)
    (hhi : 2 * n ≤ ell * ell - ell + 2) : False := by
  have hp := mul_le_mul_of_nonneg_right he (show 0 ≤ ell + 1 by linarith)
  nlinarith

/-- A finite rational remainder identity proving convexity without analysis. -/
theorem reciprocal_variance_identity
    (n x mu : ℚ) (hx : n - x ≠ 0) (hm : n - mu ≠ 0) :
    x / (n - x) - mu / (n - mu) - n / (n - mu)^2 * (x - mu) =
      n * (x - mu)^2 / ((n - x) * (n - mu)^2) := by
  field_simp
  ring

/-- The average-closeness inequality contradicts the global excess bound. -/
theorem average_bounds_impossible
    (ell e t n m C : ℚ)
    (hl : 4 ≤ ell) (he : 0 ≤ e) (hm : 0 < m)
    (hcount : m = t + e)
    (hC : ell + 1 ≤ C) (hCm : C ≤ m)
    (hlo : t + (ell + 1) * e < n)
    (hmaster : (C - ell) * n ≤ C * (1 + ell * e / m)) : False := by
  have hCpos : 0 < C := by linarith
  have hmone : 0 ≤ m - 1 := by linarith
  have hprod : 0 ≤ (m - 1) * (C - ell - 1) :=
    mul_nonneg hmone (by linarith)
  have hbound : C ≤ m * (C - ell) := by nlinarith
  have hbase : 0 < m + ell * e := by
    have : 0 ≤ ell * e := mul_nonneg (by linarith) he
    linarith
  have hnpos : 0 < n := by nlinarith [hcount]
  have hmul := mul_le_mul_of_nonneg_left hmaster (le_of_lt hm)
  have heq : m * (C * (1 + ell * e / m)) = C * (m + ell * e) := by
    field_simp
  rw [heq] at hmul
  have hmulC := mul_le_mul_of_nonneg_right hbound (le_of_lt hnpos)
  have hstrict : C * (m + ell * e) < C * n := by
    apply mul_lt_mul_of_pos_left _ hCpos
    nlinarith [hcount]
  nlinarith

#print axioms small_vertex_bounds_impossible
#print axioms reciprocal_variance_identity
#print axioms average_bounds_impossible
end LowBUG
```

### `FiniteClosenessAverage.lean`

```lean
import GraphNumericalCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
namespace LowBUG

theorem finite_inverse_jensen
    {ι : Type*} (s : Finset ι) (p : ι → ℚ) (n mu : ℚ)
    (hn : 0 ≤ n) (hm : mu < n) (hp : ∀ i ∈ s, p i < n)
    (hcenter : ∑ i ∈ s, (p i - mu) = 0) :
    (s.card : ℚ) * (mu / (n - mu)) ≤ ∑ i ∈ s, p i / (n - p i) := by
  have hpoint : ∀ i ∈ s,
      mu / (n - mu) + n / (n - mu)^2 * (p i - mu) ≤ p i / (n - p i) := by
    intro i hi
    have hx : 0 < n - p i := sub_pos.mpr (hp i hi)
    have hmu : 0 < n - mu := sub_pos.mpr hm
    have hr := reciprocal_variance_identity n (p i) mu (ne_of_gt hx) (ne_of_gt hmu)
    have hnon : 0 ≤ n * (p i - mu)^2 / ((n - p i) * (n - mu)^2) :=
      div_nonneg (mul_nonneg hn (sq_nonneg _))
        (mul_nonneg (le_of_lt hx) (sq_nonneg _))
    linarith
  have hsum := Finset.sum_le_sum hpoint
  have hlin : (∑ i ∈ s, n / (n - mu)^2 * (p i - mu)) = 0 := by
    rw [← Finset.mul_sum, hcenter, mul_zero]
  simpa only [Finset.sum_add_distrib, hlin, add_zero, Finset.sum_const,
    nsmul_eq_mul] using hsum

#print axioms finite_inverse_jensen
end LowBUG
```

### `FiniteClosenessLocal.lean`

```lean
import FiniteClosenessAverage
import Mathlib.Algebra.Order.Field.Basic

open scoped BigOperators
namespace LowBUG

theorem reciprocal_equality_forces_poles
    {ι : Type*} (s : Finset ι) (p : ι → ℚ) (n ell : ℚ)
    (hden : 0 < n - ell - 1)
    (hp : ∀ i ∈ s, p i ≤ ell + 1)
    (hcard : (s.card : ℚ) ≤ ell)
    (hsum : ∑ i ∈ s, 1 / (n - p i) = ell / (n - ell - 1)) :
    ∀ i ∈ s, p i = ell + 1 := by
  have hpoint : ∀ i ∈ s, 1 / (n - p i) ≤ 1 / (n - ell - 1) := by
    intro i hi
    exact one_div_le_one_div_of_le hden (by linarith [hp i hi])
  have hb : 0 ≤ 1 / (n - ell - 1) := le_of_lt (one_div_pos.mpr hden)
  have hs : (∑ i ∈ s, (1 / (n - ell - 1) - 1 / (n - p i))) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum]
    have hmul := mul_le_mul_of_nonneg_right hcard hb
    simpa only [div_eq_mul_inv, one_mul] using sub_nonpos.mpr hmul
  intro i hi
  have hsingle := Finset.single_le_sum
    (fun j hj => sub_nonneg.mpr (hpoint j hj)) hi
  have heq : 1 / (n - ell - 1) = 1 / (n - p i) := by
    linarith [hpoint i hi]
  have hpi : n - p i ≠ 0 := ne_of_gt (by linarith [hp i hi])
  have hne : n - ell - 1 ≠ 0 := ne_of_gt hden
  field_simp at heq
  linarith

#print axioms reciprocal_equality_forces_poles
end LowBUG
```

### `FiniteClosenessLowerBound.lean`

```lean
import FiniteClosenessLocal
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace LowBUG

lemma finite_reciprocal_upper
    {ι : Type*} (s : Finset ι) (p : ι → ℕ) (n : ℚ) (K : ℕ)
    (hden : 0 < n - K) (hp : ∀ i ∈ s, p i ≤ K) :
    (∑ i ∈ s, 1 / (n - (p i : ℚ))) ≤ (s.card : ℚ) / (n - K) := by
  calc
    (∑ i ∈ s, 1 / (n - (p i : ℚ))) ≤ ∑ _i ∈ s, 1 / (n - K) := by
      apply Finset.sum_le_sum
      intro i hi
      exact one_div_le_one_div_of_le hden
        (by have hh : (p i : ℚ) ≤ K := by exact_mod_cast hp i hi
            linarith)
    _ = (s.card : ℚ) / (n - K) := by simp [div_eq_mul_inv, nsmul_eq_mul]

theorem low_closeness_impossible
    {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (ell cap D degree : ℕ) (e t n : ℚ)
    (hl : 4 ≤ ell) (ht : 1 ≤ t)
    (hcap : ell < cap) (hDelta : 2 * D ≤ cap)
    (hden : 0 < n - ell - 1)
    (hsmall : s.card ≤ ell) (hdegree : 2 * degree ≤ s.card)
    (hp : ∀ i ∈ s, p i ≤ 2 * D)
    (hpexcess : ∀ i ∈ s, (p i : ℚ) - 4 ≤ 2 * e)
    (hincident : ∃ i ∈ s, p i ≤ degree + D)
    (hlo : (e + 1) * ((ell : ℚ) + 1) + t ≤ n)
    (hhi : ((cap : ℚ) - ell) * n ≤ cap * ((ell : ℚ) + 1) - 4 * ell)
    (hsum : ∑ i ∈ s, 1 / (n - (p i : ℚ)) =
      (ell : ℚ) / (n - ell - 1)) : False := by
  have hlarge : ∃ i ∈ s, ell + 1 ≤ p i := by
    by_contra hnot
    have hall : ∀ i ∈ s, p i ≤ ell := by
      intro i hi
      by_contra hb
      exact hnot ⟨i, hi, by omega⟩
    have hupper := finite_reciprocal_upper s p n ell (by linarith) hall
    have hcard : (s.card : ℚ) ≤ ell := by exact_mod_cast hsmall
    have hdiv : (s.card : ℚ) / (n - ell) ≤ (ell : ℚ) / (n - ell) :=
      div_le_div_of_nonneg_right hcard (by linarith)
    have hrec := one_div_lt_one_div_of_lt hden
      (show n - ell - 1 < n - ell by linarith)
    have helpos : (0 : ℚ) < ell := by exact_mod_cast (show 0 < ell by omega)
    have hstrict := mul_lt_mul_of_pos_left hrec helpos
    simp only [div_eq_mul_inv, one_mul] at hupper hdiv hsum hstrict
    linarith
  obtain ⟨i, hi, hip⟩ := hlarge
  have hex : (ell : ℚ) - 3 ≤ 2 * e := by
    have hh : (ell : ℚ) + 1 ≤ p i := by exact_mod_cast hip
    linarith [hpexcess i hi]
  have hc_eq : cap = ell + 1 := by
    by_contra hcnot
    have hc2 : ell + 2 ≤ cap := by omega
    have hc2q : (ell : ℚ) + 2 ≤ cap := by exact_mod_cast hc2
    have hprod := mul_le_mul_of_nonneg_right
      (show (2 : ℚ) ≤ (cap : ℚ) - ell by linarith) (le_of_lt hden)
    have hnhi : 2 * n ≤ (ell : ℚ) * ell - ell + 2 := by
      nlinarith [hhi, hprod]
    exact small_vertex_bounds_impossible ell e t n (by exact_mod_cast hl) ht hex hlo hnhi
  have hpcap : ∀ i ∈ s, (p i : ℚ) ≤ (ell : ℚ) + 1 := by
    intro i hi
    have hh : p i ≤ ell + 1 := by have := hp i hi; omega
    exact_mod_cast hh
  have hequality := reciprocal_equality_forces_poles s (fun i => (p i : ℚ)) n ell
    hden hpcap (by exact_mod_cast hsmall) hsum
  obtain ⟨j, hj, hjp⟩ := hincident
  have hj_eq : p j = ell + 1 := by exact_mod_cast hequality j hj
  omega

#print axioms low_closeness_impossible
end LowBUG
```

### `BetweennessParameters.lean`

```lean
import BetweennessLocal
import BetweennessEdgeBounds
import FiniteClosenessLowerBound

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma exotic_co_value (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (l : ℕ) (hs : ∃ J, StarComponent Gᶜ l J) (v : Fin n) :
    coBetweenness Gᶜ v = (l : ℚ) / ((n : ℚ) - l - 1) := by
  obtain ⟨J, hj⟩ := hs
  rw [(lowBUG_reduction G h).2.2.2 v hj.choose]
  exact star_coBetweenness Gᶜ J l hj hj.choose hj.choose_spec.1

lemma exotic_n_gt_four (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K) : 4 < n := by
  classical
  obtain ⟨v, hv⟩ := K.nonempty_supp
  have hd := exotic_min_degree G h K hk v hv
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (Gᶜ.neighborFinset v).card by change 0 < Gᶜ.degree v; omega)
  have hvu : Gᶜ.Adj v u := by simpa using hu
  exact lt_of_le_of_lt (exotic_pole_four G h K hk hv hvu)
    (pole_lt_of_diameterTwo G (lowBUG_diameterTwo G h) hvu)

lemma exotic_co_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ l, StarComponent Gᶜ l K)
    (v : Fin n) (hv : v ∈ K.supp) :
    ((closeEdges Gᶜ v).card : ℚ) / ((n : ℚ) - 4) ≤ coBetweenness Gᶜ v := by
  classical
  have hsum : ∑ _e ∈ closeEdges Gᶜ v, (1 : ℚ) / ((n : ℚ) - 4) =
      ((closeEdges Gᶜ v).card : ℚ) / ((n : ℚ) - 4) := by simp [div_eq_mul_inv]
  rw [← hsum]
  apply Finset.sum_le_sum
  intro e he
  have hK := (Finset.mem_filter.mp (closeEdges_subset_component Gᶜ K hv he)).2
  have hadj := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2
  have hp := exotic_pole_four G h K hk hK hadj
  have hpn := pole_lt_of_diameterTwo G (lowBUG_diameterTwo G h) hadj
  have hpq : (4 : ℚ) ≤ pole Gᶜ e.1 e.2 := by exact_mod_cast hp
  have hpnq : (pole Gᶜ e.1 e.2 : ℚ) < n := by exact_mod_cast hpn
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma exotic_star_size_ge_four (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ k, StarComponent Gᶜ k K)
    (l : ℕ) (hs : ∃ J, StarComponent Gᶜ l J) : 4 ≤ l := by
  obtain ⟨v, hv⟩ := K.nonempty_supp
  have hn := exotic_n_gt_four G h K hk
  have hnq : (4 : ℚ) < n := by exact_mod_cast hn
  obtain ⟨J, hj⟩ := hs
  have hln := star_size_lt_of_lowBUG G h J l hj (by omega)
  have hlnq : (l : ℚ) + 1 < n := by exact_mod_cast hln
  have hd := exotic_min_degree G h K hk v hv
  have hc := exotic_degree_close G h K hk v hv
  have hcq : (4 : ℚ) ≤ (closeEdges Gᶜ v).card := by exact_mod_cast (show 4 ≤ (closeEdges Gᶜ v).card by omega)
  have hb := exotic_co_lower G h K hk v hv
  rw [exotic_co_value G h l ⟨J, hj⟩] at hb
  have he := (div_le_div_iff₀ (by linarith : (0 : ℚ) < n - 4)
    (by linarith : (0 : ℚ) < n - l - 1)).mp hb
  by_contra hh
  have hlq : (l : ℚ) ≤ 3 := by exact_mod_cast (show l ≤ 3 by omega)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcq) (show (0 : ℚ) ≤ n - l - 1 by linarith),
    mul_nonneg (show (0 : ℚ) ≤ 3 - l by linarith) (show (0 : ℚ) ≤ n - 4 by linarith)]

lemma exotic_max_data (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ k, StarComponent Gᶜ k K)
    (l : ℕ) (hs : ∃ J, StarComponent Gᶜ l J) :
    ∃ cap D : ℕ, l < cap ∧ 2 * D ≤ cap ∧
      (∀ v ∈ K.supp, Gᶜ.degree v ≤ D) ∧
      (∀ v ∈ K.supp, (closeEdges Gᶜ v).card ≤ cap) ∧
      (((cap : ℚ) - l) * n ≤ (cap : ℚ) * (l + 1) - 4 * l) := by
  classical
  have hne : K.supp.toFinset.Nonempty := by simpa using K.nonempty_supp
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image K.supp.toFinset (fun v => (closeEdges Gᶜ v).card) hne
  obtain ⟨w, hw, hD⟩ := Finset.exists_max_image K.supp.toFinset (fun u => Gᶜ.degree u) hne
  let cap := (closeEdges Gᶜ v).card
  let D := Gᶜ.degree w
  have hvK := Set.mem_toFinset.mp hv
  have hn := exotic_n_gt_four G h K hk
  have hl := exotic_star_size_ge_four G h K hk l hs
  obtain ⟨J, hj⟩ := hs
  have hln := star_size_lt_of_lowBUG G h J l hj (by omega)
  have hlnq : (l : ℚ) + 1 < n := by exact_mod_cast hln
  have hnq : (4 : ℚ) < n := by exact_mod_cast hn
  have hDelta : 2 * D ≤ cap :=
    (exotic_degree_close G h K hk w (Set.mem_toFinset.mp hw)).trans (hmax w hw)
  have hdegrees : ∀ u ∈ K.supp, Gᶜ.degree u ≤ D := fun u hu => hD u (Set.mem_toFinset.mpr hu)
  have hp : ∀ e ∈ closeEdges Gᶜ v, pole Gᶜ e.1 e.2 ≤ 2 * D := by
    intro e he
    have heK := Finset.mem_filter.mp (closeEdges_subset_component Gᶜ K hvK he)
    have hadj := (Finset.mem_filter.mp heK.1).2.2
    have hbK := K.mem_supp_of_adj_mem_supp heK.2 hadj
    exact (pole_le_degree_sum Gᶜ _ _).trans (by have := hdegrees e.1 heK.2; have := hdegrees e.2 hbK; omega)
  have hcap : l < cap := by
    by_contra hh
    have hcl : cap ≤ l := by omega
    have hu := LowBUG.finite_reciprocal_upper (closeEdges Gᶜ v)
      (fun e => pole Gᶜ e.1 e.2) (n : ℚ) l (by linarith)
      (fun e he => (hp e he).trans (hDelta.trans hcl))
    change coBetweenness Gᶜ v ≤ (cap : ℚ) / ((n : ℚ) - l) at hu
    rw [exotic_co_value G h l ⟨J, hj⟩] at hu
    have he := (div_le_div_iff₀ (by linarith : (0 : ℚ) < n - l - 1)
      (by linarith : (0 : ℚ) < n - l)).mp hu
    have hclq : (cap : ℚ) ≤ l := by exact_mod_cast hcl
    have hlq : (4 : ℚ) ≤ l := by exact_mod_cast hl
    nlinarith [mul_nonneg (sub_nonneg.mpr hclq) (show (0 : ℚ) ≤ n - l - 1 by linarith)]
  have hlow := exotic_co_lower G h K hk v hvK
  rw [exotic_co_value G h l ⟨J, hj⟩] at hlow
  have he := (div_le_div_iff₀ (by linarith : (0 : ℚ) < n - 4)
    (by linarith : (0 : ℚ) < n - l - 1)).mp hlow
  refine ⟨cap, D, hcap, hDelta, hdegrees, ?_, ?_⟩
  · intro u hu; exact hmax u (Set.mem_toFinset.mpr hu)
  · change (cap : ℚ) * ((n : ℚ) - l - 1) ≤ (l : ℚ) * ((n : ℚ) - 4) at he
    nlinarith

#print axioms exotic_star_size_ge_four
#print axioms exotic_max_data
end Betweenness
```

### `BetweennessClosenessLower.lean`

```lean
import BetweennessParameters

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

lemma exotic_closeness_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (hk : ¬ ∃ k, StarComponent Gᶜ k K)
    (l : ℕ) (hs : ∃ J, StarComponent Gᶜ l J) :
    ∀ v ∈ K.supp, l + 1 ≤ (closeEdges Gᶜ v).card := by
  classical
  have hl := exotic_star_size_ge_four G h K hk l hs
  have hn := exotic_n_gt_four G h K hk
  have ht : 0 < K.supp.ncard := (Set.ncard_pos (Set.toFinite _)).mpr K.nonempty_supp
  have hm := nonstar_component_edges_ge_vertices G h K hk
  have hlo := exotic_star_count G h K hk l hs
  obtain ⟨J, hj⟩ := hs
  have hln := star_size_lt_of_lowBUG G h J l hj (by omega)
  have hlnq : (l : ℚ) + 1 < n := by exact_mod_cast hln
  obtain ⟨cap, D, hcap, hDelta, hdegrees, _hcards, hhi⟩ := exotic_max_data G h K hk l ⟨J, hj⟩
  intro v hv
  by_contra hh
  have hsmall : (closeEdges Gᶜ v).card ≤ l := by omega
  have hdeg := exotic_degree_close G h K hk v hv
  have heK : ∀ e ∈ closeEdges Gᶜ v, e.1 ∈ K.supp ∧ e.2 ∈ K.supp ∧ Gᶜ.Adj e.1 e.2 := by
    intro e he
    have hh := Finset.mem_filter.mp (closeEdges_subset_component Gᶜ K hv he)
    have hadj := (Finset.mem_filter.mp hh.1).2.2
    exact ⟨hh.2, K.mem_supp_of_adj_mem_supp hh.2 hadj, hadj⟩
  apply LowBUG.low_closeness_impossible (closeEdges Gᶜ v)
    (fun e => pole Gᶜ e.1 e.2) l cap D (Gᶜ.degree v)
    (((componentEdges Gᶜ K).card - K.supp.ncard : ℕ) : ℚ) (K.supp.ncard : ℚ) (n : ℚ)
    hl (by exact_mod_cast ht) hcap hDelta (by linarith) hsmall hdeg
  · intro e he
    have h1 := hdegrees e.1 (heK e he).1
    have h2 := hdegrees e.2 (heK e he).2.1
    exact (pole_le_degree_sum Gᶜ _ _).trans (by omega)
  · intro e he
    have hp := (pole_le_degree_sum Gᶜ e.1 e.2).trans
      (edge_degree_excess_bound G h K hk (heK e he).1 (heK e he).2.2)
    have hpq : (pole Gᶜ e.1 e.2 : ℚ) ≤
        2 * (((componentEdges Gᶜ K).card - K.supp.ncard : ℕ) : ℚ) + 4 := by exact_mod_cast hp
    linarith
  · have hd := exotic_min_degree G h K hk v hv
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (Gᶜ.neighborFinset v).card by change 0 < Gᶜ.degree v; omega)
    have hvu : Gᶜ.Adj v u := by simpa using hu
    have huK := K.mem_supp_of_adj_mem_supp hv hvu
    obtain ⟨e, he, heq⟩ := adjacent_close_pair Gᶜ hvu
    refine ⟨e, he, ?_⟩
    have hp := pole_le_degree_sum Gᶜ e.1 e.2
    have hDu := hdegrees u huK
    rcases heq with ⟨he1, he2⟩ | ⟨he1, he2⟩ <;> rw [he1, he2] at hp ⊢ <;> omega
  · have hlo' : ((componentEdges Gᶜ K).card - K.supp.ncard + 1) * (l + 1) + K.supp.ncard ≤ n := by omega
    exact_mod_cast hlo'
  · exact hhi
  · exact exotic_co_value G h l ⟨J, hj⟩ v

#print axioms exotic_closeness_lower
end Betweenness
```

### `FiniteClosenessObstruction.lean`

```lean
import FiniteClosenessAverage
import Mathlib.Algebra.Order.Field.Basic

open scoped BigOperators
namespace LowBUG

theorem finite_average_obstruction
    {ι : Type*} (s : Finset ι) (p : ι → ℚ)
    (ell e t n m C : ℚ)
    (hl : 4 ≤ ell) (he : 0 ≤ e) (ht : 0 < t)
    (hm : 0 < m) (hmcard : (s.card : ℚ) = m)
    (hmcount : m = t + e)
    (hC : ell + 1 ≤ C) (hCm : C ≤ m)
    (htn : t < n) (helln : ell + 1 < n)
    (hp : ∀ i ∈ s, p i < n)
    (hsump : ∑ i ∈ s, p i = t * C)
    (hsumf : ∑ i ∈ s, p i / (n - p i) = t * ell / (n - ell - 1))
    (hlo : t + (ell + 1) * e < n) : False := by
  let mu := t * C / m
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmu_le : mu ≤ t := by
    dsimp [mu]
    apply (div_le_iff₀ hm).mpr
    exact mul_le_mul_of_nonneg_left hCm (le_of_lt ht)
  have hmu : mu < n := lt_of_le_of_lt hmu_le htn
  have hcenter : ∑ i ∈ s, (p i - mu) = 0 := by
    rw [Finset.sum_sub_distrib, hsump, Finset.sum_const, nsmul_eq_mul, hmcard]
    dsimp [mu]
    field_simp
    ring
  have hj := finite_inverse_jensen s p n mu (by linarith) hmu hp hcenter
  rw [hmcard, hsumf] at hj
  have hleft : m * (mu / (n - mu)) = (t * C) / (n - mu) := by
    dsimp [mu]
    field_simp
  rw [hleft] at hj
  have hcross := (div_le_div_iff₀ (sub_pos.mpr hmu)
    (show 0 < n - ell - 1 by linarith)).mp hj
  have hcancel : C * (n - ell - 1) ≤ ell * (n - mu) := by
    by_contra hbad
    have hz : 0 < t * (C * (n - ell - 1) - ell * (n - mu)) :=
      mul_pos ht (by linarith)
    nlinarith [hcross]
  have heqm : ell * mu = C * (ell - ell * e / m) := by
    dsimp [mu]
    field_simp
    nlinarith [hmcount]
  have hmaster : (C - ell) * n ≤ C * (1 + ell * e / m) := by
    nlinarith [hcancel, heqm]
  exact average_bounds_impossible ell e t n m C hl he hm hmcount hC hCm hlo hmaster

#print axioms finite_average_obstruction
end LowBUG
```

### `BetweennessComponentObstruction.lean`

```lean
import BetweennessLowDiameter
import BetweennessDoubleCount
import FiniteClosenessObstruction

open scoped BigOperators
namespace Betweenness
variable {n : ℕ}

/-- Conditional graph form of the new Jensen/excess obstruction. The component
structure and lower-closeness hypotheses are supplied by the classification module. -/
theorem component_average_obstruction (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (K : Gᶜ.ConnectedComponent) (l : ℕ)
    (hl : 4 ≤ l)
    (ht : 0 < K.supp.ncard) (htn : K.supp.ncard < n)
    (hm : K.supp.ncard ≤ (componentEdges Gᶜ K).card)
    (helln : l + 1 < n)
    (hlo : K.supp.ncard +
      (((componentEdges Gᶜ K).card - K.supp.ncard) + 1) * (l + 1) ≤ n)
    (hc : ∀ v ∈ K.supp, l + 1 ≤ (closeEdges Gᶜ v).card)
    (hq : ∀ v ∈ K.supp, coBetweenness Gᶜ v =
      (l : ℚ) / ((n : ℚ) - l - 1)) : False := by
  classical
  let s := componentEdges Gᶜ K
  let t : ℚ := K.supp.ncard
  let m : ℚ := s.card
  let e : ℚ := m - t
  let C : ℚ := (∑ v ∈ K.supp.toFinset, ((closeEdges Gᶜ v).card : ℚ)) / t
  have htc : (K.supp.toFinset.card : ℚ) = t := by
    dsimp [t]
    rw [Set.ncard_eq_toFinset_card']
  have htq : 0 < t := by dsimp [t]; exact_mod_cast ht
  have hmq : 0 < m := by dsimp [m, s]; exact_mod_cast lt_of_lt_of_le ht hm
  have heq : 0 ≤ e := by
    dsimp [e, m, t, s]
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  have hClow : (l : ℚ) + 1 ≤ C := by
    apply (le_div_iff₀ htq).mpr
    have hh : ∑ _v ∈ K.supp.toFinset, ((l : ℚ) + 1) ≤
        ∑ v ∈ K.supp.toFinset, ((closeEdges Gᶜ v).card : ℚ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact_mod_cast hc v (Set.mem_toFinset.mp hv)
    simpa only [Finset.sum_const, nsmul_eq_mul, htc, mul_comm] using hh
  have hCm : C ≤ m := by
    apply (div_le_iff₀ htq).mpr
    have hh : (∑ v ∈ K.supp.toFinset, ((closeEdges Gᶜ v).card : ℚ)) ≤
        ∑ _v ∈ K.supp.toFinset, m := by
      apply Finset.sum_le_sum
      intro v hv
      have hsub : closeEdges Gᶜ v ⊆ s := by
        intro ab hab
        obtain ⟨hab, hclose⟩ := Finset.mem_filter.mp hab
        have hadj := (Finset.mem_filter.mp hab).2.2
        have hk := (close_component_iff Gᶜ K hadj hclose).mp (Set.mem_toFinset.mp hv)
        exact Finset.mem_filter.mpr ⟨hab, hk⟩
      dsimp [m]
      exact_mod_cast Finset.card_le_card hsub
    simpa only [Finset.sum_const, nsmul_eq_mul, htc, mul_comm] using hh
  have hsump : ∑ ab ∈ s, (pole Gᶜ ab.1 ab.2 : ℚ) = t * C := by
    have hh := close_double_count Gᶜ K
    have hhq : (∑ v ∈ K.supp.toFinset, ((closeEdges Gᶜ v).card : ℚ)) =
        ∑ ab ∈ s, (pole Gᶜ ab.1 ab.2 : ℚ) := by exact_mod_cast hh
    rw [← hhq]
    dsimp [C]
    exact (mul_div_cancel₀ _ (ne_of_gt htq)).symm
  have hsumf : ∑ ab ∈ s, (pole Gᶜ ab.1 ab.2 : ℚ) /
      ((n : ℚ) - pole Gᶜ ab.1 ab.2) = t * l / ((n : ℚ) - l - 1) := by
    have hh := co_double_count Gᶜ K
    have hh' : ∑ v ∈ K.supp.toFinset, coBetweenness Gᶜ v =
        ∑ ab ∈ s, (pole Gᶜ ab.1 ab.2 : ℚ) / ((n : ℚ) - pole Gᶜ ab.1 ab.2) := by
      simpa only [weight, div_eq_mul_inv, one_mul] using hh
    rw [← hh']
    rw [Finset.sum_congr rfl (fun v hv => hq v (Set.mem_toFinset.mp hv)),
      Finset.sum_const, nsmul_eq_mul, htc, mul_div_assoc]
  have hpn : ∀ ab ∈ s, (pole Gᶜ ab.1 ab.2 : ℚ) < n := by
    intro ab hab
    have hadj := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2.2
    exact_mod_cast pole_lt_of_diameterTwo G (lowBUG_diameterTwo G h) hadj
  have hloq : t + ((l : ℚ) + 1) * e < n := by
    have hh : t + (e + 1) * ((l : ℚ) + 1) ≤ n := by
      dsimp [t, e, m, s]
      exact_mod_cast hlo
    nlinarith
  apply LowBUG.finite_average_obstruction s (fun ab => (pole Gᶜ ab.1 ab.2 : ℚ))
    l e t n m C (by exact_mod_cast hl) heq htq hmq rfl (by dsimp [e]; ring)
    hClow hCm (by dsimp [t]; exact_mod_cast htn) (by exact_mod_cast helln) hpn hsump hsumf hloq

#print axioms component_average_obstruction
end Betweenness
```

### `BetweennessObstructionData.lean`

```lean
import BetweennessComponentObstruction

namespace Betweenness
variable {n : ℕ}

/-- Explicit finite graph data produced by `counterexample_component_data`.
This definition is not the definition of `LowBUG` or of the conjecture. -/
def ObstructionComponent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ (K : Gᶜ.ConnectedComponent) (l : ℕ),
    4 ≤ l ∧ 0 < K.supp.ncard ∧ K.supp.ncard < n ∧
    K.supp.ncard ≤ (componentEdges Gᶜ K).card ∧ l + 1 < n ∧
    K.supp.ncard + (((componentEdges Gᶜ K).card - K.supp.ncard) + 1) * (l + 1) ≤ n ∧
    (∀ v ∈ K.supp, l + 1 ≤ (closeEdges Gᶜ v).card) ∧
    (∀ v ∈ K.supp, coBetweenness Gᶜ v = (l : ℚ) / ((n : ℚ) - l - 1))

theorem lowBUG_no_obstruction_component (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) : ¬ ObstructionComponent G := by
  rintro ⟨K, l, hl, ht, htn, hm, helln, hlo, hc, hq⟩
  exact component_average_obstruction G h K l hl ht htn hm helln hlo hc hq

#print axioms lowBUG_no_obstruction_component
end Betweenness
```

### `BetweennessClassification.lean`

```lean
import BetweennessClosenessLower
import BetweennessObstructionData

namespace Betweenness
variable {n : ℕ}

lemma counterexample_component_data (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (hn : ¬ EqualStarUnion Gᶜ) : ObstructionComponent G := by
  classical
  obtain ⟨l, hs, heq, _hsmall⟩ := star_component_reduction G h
  have hex : ∃ K : Gᶜ.ConnectedComponent, ¬ ∃ k, StarComponent Gᶜ k K := by
    by_contra hh
    push Not at hh
    apply hn
    refine ⟨l, ?_⟩
    intro K
    obtain ⟨k, hk⟩ := hh K
    exact heq K k hk ▸ hk
  obtain ⟨K, hk⟩ := hex
  have hl := exotic_star_size_ge_four G h K hk l hs
  have ht : 0 < K.supp.ncard := (Set.ncard_pos (Set.toFinite _)).mpr K.nonempty_supp
  have hm := nonstar_component_edges_ge_vertices G h K hk
  have hlo := exotic_star_count G h K hk l hs
  have htn : K.supp.ncard < n := by nlinarith
  obtain ⟨J, hj⟩ := hs
  have hln := star_size_lt_of_lowBUG G h J l hj (by omega)
  exact ⟨K, l, hl, ht, htn, hm, hln, hlo,
    exotic_closeness_lower G h K hk l ⟨J, hj⟩,
    fun v _ => exotic_co_value G h l ⟨J, hj⟩ v⟩

theorem exotic_impossible (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : LowBUG G) (hn : ¬ EqualStarUnion Gᶜ) : False :=
  lowBUG_no_obstruction_component G h (counterexample_component_data G h hn)

theorem lowBUG_complement_equal_stars (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : LowBUG G) : EqualStarUnion Gᶜ := by
  by_contra hn
  exact exotic_impossible G h hn

#print axioms lowBUG_complement_equal_stars
#print lowBUG_complement_equal_stars
end Betweenness
```

### `BetweennessGuards.lean`

```lean
import BetweennessDiameterTwo
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace Betweenness

/-- Path on three vertices with centre 0. -/
def pathThree : SimpleGraph (Fin 3) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩
instance : DecidableRel pathThree.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma pathThree_diameterTwo : DiameterTwo pathThree := by unfold DiameterTwo; decide
lemma pathThree_centre : betweenness pathThree 0 = 1 := by
  rw [betweenness_eq_twoBetweenness _ pathThree_diameterTwo]
  simp only [twoBetweenness, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fin.sum_univ_succ]
  norm_num [pathThree, SimpleGraph.commonNeighbors, SimpleGraph.neighborSet]

/-- Disjoint union of two K1,2's on consecutive triples. -/
def twoStars : SimpleGraph (Fin 6) where
  Adj a b := a ≠ b ∧ a.val / 3 = b.val / 3 ∧ (a.val % 3 = 0 ∨ b.val % 3 = 0)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩
instance : DecidableRel twoStars.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
lemma twoStars_compl_diameterTwo : DiameterTwo twoStarsᶜ := by unfold DiameterTwo; decide
lemma twoStars_compl_betweenness (x : Fin 6) : betweenness twoStarsᶜ x = 2/3 := by
  rw [betweenness_eq_twoBetweenness _ twoStars_compl_diameterTwo]
  fin_cases x <;> simp only [twoBetweenness, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fin.sum_univ_succ] <;>
    norm_num [twoStars, SimpleGraph.compl_adj, SimpleGraph.commonNeighbors, SimpleGraph.neighborSet]

/-- The cycle C5. It has value ONE, correcting the review's proposed 1/2. -/
def cycleFive : SimpleGraph (Fin 5) where
  Adj a b := (a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by intro a; fin_cases a <;> decide⟩
instance : DecidableRel cycleFive.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
lemma cycleFive_diameterTwo : DiameterTwo cycleFive := by unfold DiameterTwo; decide
lemma cycleFive_betweenness (x : Fin 5) : betweenness cycleFive x = 1 := by
  rw [betweenness_eq_twoBetweenness _ cycleFive_diameterTwo]
  fin_cases x <;> simp only [twoBetweenness, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fin.sum_univ_succ] <;>
    norm_num [cycleFive, SimpleGraph.commonNeighbors, SimpleGraph.neighborSet]
lemma cycleFive_not_half : betweenness cycleFive 0 ≠ 1/2 := by
  rw [cycleFive_betweenness]; norm_num

lemma disconnected_zero (x : Fin 2) : betweenness (⊥ : SimpleGraph (Fin 2)) x = 0 := by
  have ht : ∀ v w, sigmaThrough (⊥ : SimpleGraph (Fin 2)) v w x = 0 := by
    intro v w
    apply sigmaThrough_eq_zero_of_dist_le_one
    simp
  unfold betweenness
  simp only [ht, Nat.cast_zero, zero_div, ite_self, Finset.sum_const_zero]

lemma disconnected_not_connected : ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by
  intro h
  have hp := h.pos_dist_of_ne (by decide : (0 : Fin 2) ≠ 1)
  simp at hp
lemma disconnected_not_lowBUG : ¬ LowBUG (⊥ : SimpleGraph (Fin 2)) := by
  intro h
  exact disconnected_not_connected h.1

/-- A raw rational weight is zero here, but the requisite strict bound fails. -/
lemma full_close_edge_guard : pathThree.Adj 0 1 ∧ pole pathThree 0 1 = 3 ∧
    weight pathThree 0 1 = 0 ∧ ¬ pole pathThree 0 1 < 3 := by
  have hp : pole pathThree 0 1 = 3 := by decide
  refine ⟨by decide, hp, ?_, by omega⟩
  norm_num [weight, hp]

/-- One isolated vertex and one edge: stars of different sizes. -/
def mixedStars : SimpleGraph (Fin 3) where
  Adj a b := a ≠ b ∧ a ≠ 0 ∧ b ≠ 0
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩
instance : DecidableRel mixedStars.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma mixedStars_supp_zero : (mixedStars.connectedComponentMk 0).supp = {0} := by
  ext v
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, Set.mem_singleton_iff]
  fin_cases v <;> decide
lemma mixedStars_supp_one : (mixedStars.connectedComponentMk 1).supp = {1, 2} := by
  ext v
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases v <;> decide

lemma mixedStars_not_equal : ¬ EqualStarUnion mixedStars := by
  rintro ⟨l, h⟩
  obtain ⟨c, hc, hcard, _⟩ := h (mixedStars.connectedComponentMk 0)
  obtain ⟨d, hd, hcard', _⟩ := h (mixedStars.connectedComponentMk 1)
  rw [mixedStars_supp_zero, Set.ncard_singleton] at hcard
  rw [mixedStars_supp_one] at hcard'
  norm_num at hcard'
  omega

lemma mixedStars_star_zero : StarComponent mixedStars 0 (mixedStars.connectedComponentMk 0) := by
  refine ⟨0, ?_, ?_, ?_⟩
  · rw [mixedStars_supp_zero]; decide
  · rw [mixedStars_supp_zero]; simp
  · rw [mixedStars_supp_zero]
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    subst u; subst v; decide
lemma mixedStars_star_one : StarComponent mixedStars 1 (mixedStars.connectedComponentMk 1) := by
  refine ⟨1, ?_, ?_, ?_⟩
  · rw [mixedStars_supp_one]; decide
  · rw [mixedStars_supp_one]; norm_num
  · rw [mixedStars_supp_one]
    intro u hu v hv
    fin_cases u <;> fin_cases v <;> simp_all [mixedStars]
lemma mixedStars_componentwise : ∀ K : mixedStars.ConnectedComponent,
    ∃ l, StarComponent mixedStars l K := by
  intro K
  induction K using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    fin_cases v
    · exact ⟨0, mixedStars_star_zero⟩
    · exact ⟨1, mixedStars_star_one⟩
    · have he : mixedStars.connectedComponentMk 2 = mixedStars.connectedComponentMk 1 := by
        apply SimpleGraph.ConnectedComponent.eq.mpr
        exact (show mixedStars.Adj 2 1 by decide).reachable
      exact ⟨1, he.symm ▸ mixedStars_star_one⟩

lemma complement_two_sizes_guard :
    (∀ K : (mixedStarsᶜ)ᶜ.ConnectedComponent, ∃ l, StarComponent (mixedStarsᶜ)ᶜ l K) ∧
    ¬ EqualStarUnion (mixedStarsᶜ)ᶜ := by
  have he : (mixedStarsᶜ)ᶜ = mixedStars := by
    ext u v
    simp only [SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hne, hh⟩
      by_contra ha
      exact hh ⟨hne, ha⟩
    · intro ha
      exact ⟨ha.ne, fun hh => hh.2 ha⟩
  rw [he]
  exact ⟨mixedStars_componentwise, mixedStars_not_equal⟩

#print axioms complement_two_sizes_guard

#print axioms pathThree_centre
#print axioms twoStars_compl_betweenness
#print axioms cycleFive_betweenness
#print axioms disconnected_not_lowBUG
#print axioms full_close_edge_guard
#print axioms mixedStars_not_equal
#print axioms mixedStars_componentwise
end Betweenness
```

### `BetweennessNonvacuity.lean`

```lean
import BetweennessGuards

namespace Betweenness

theorem twoStars_compl_lowBUG : LowBUG twoStarsᶜ := by
  refine ⟨diameterTwo_connected twoStarsᶜ twoStars_compl_diameterTwo, ?_, ?_⟩
  · intro x y
    rw [twoStars_compl_betweenness x, twoStars_compl_betweenness y]
  · intro x
    rw [twoStars_compl_betweenness x]
    norm_num

#print axioms twoStars_compl_lowBUG
end Betweenness
```

### `BetweennessAudit.lean`

```lean
import BetweennessDefinitions
import BetweennessCounting
import BetweennessTotal
import BetweennessSimplicial
import BetweennessLowDiameter
import BetweennessDiameterTwo
import BetweennessComplement
import BetweennessReduction
import BetweennessCloseOrder
import BetweennessLeaf
import BetweennessStarExistence
import BetweennessDoubleCount
import BetweennessStarValue
import BetweennessStarReduction
import BetweennessComponentCounts
import BetweennessExcess
import BetweennessUniformComponent
import BetweennessTriangle
import BetweennessIncidence
import BetweennessLocal
import BetweennessEdgeBounds
import GraphNumericalCore
import FiniteClosenessAverage
import FiniteClosenessLocal
import FiniteClosenessLowerBound
import BetweennessParameters
import BetweennessClosenessLower
import FiniteClosenessObstruction
import BetweennessComponentObstruction
import BetweennessObstructionData
import BetweennessClassification
import BetweennessGuards
import BetweennessNonvacuity

#eval Lean.versionString
#check Betweenness.sigma_pos
#print axioms Betweenness.sigma_pos
#check Betweenness.shortest_isPath
#print axioms Betweenness.shortest_isPath
#check Betweenness.sigma_eq_commonNeighbors
#print axioms Betweenness.sigma_eq_commonNeighbors
#check Betweenness.walk_two_internal
#print axioms Betweenness.walk_two_internal
#check Betweenness.sigmaThrough_eq_of_dist_two
#print axioms Betweenness.sigmaThrough_eq_of_dist_two
#check Betweenness.sigmaThrough_eq_zero_of_dist_le_one
#print axioms Betweenness.sigmaThrough_eq_zero_of_dist_le_one
#check Betweenness.diameterTwo_dist
#print axioms Betweenness.diameterTwo_dist
#check Betweenness.diameterTwo_connected
#print axioms Betweenness.diameterTwo_connected
#check Betweenness.internal_count
#print axioms Betweenness.internal_count
#check Betweenness.sigmaThrough_sum
#print axioms Betweenness.sigmaThrough_sum
#check Betweenness.total_betweenness
#print axioms Betweenness.total_betweenness
#check Betweenness.complement_edge_bound
#print axioms Betweenness.complement_edge_bound
#check Betweenness.lowBUG_sparse
#print axioms Betweenness.lowBUG_sparse
#check Betweenness.shortest_no_internal_of_clique
#print axioms Betweenness.shortest_no_internal_of_clique
#check Betweenness.betweenness_zero_of_clique
#print axioms Betweenness.betweenness_zero_of_clique
#check Betweenness.lowBUG_complete_of_zero
#print axioms Betweenness.lowBUG_complete_of_zero
#check Betweenness.pairs_card_eq_edgeSet
#print axioms Betweenness.pairs_card_eq_edgeSet
#check Betweenness.centreEdges_le
#print axioms Betweenness.centreEdges_le
#check Betweenness.centreEdges_connected
#print axioms Betweenness.centreEdges_connected
#check Betweenness.lowBUG_diameterTwo
#print axioms Betweenness.lowBUG_diameterTwo
#check Betweenness.dist_two_of_diameterTwo
#print axioms Betweenness.dist_two_of_diameterTwo
#check Betweenness.contribution_diameterTwo
#print axioms Betweenness.contribution_diameterTwo
#check Betweenness.betweenness_eq_twoBetweenness
#print axioms Betweenness.betweenness_eq_twoBetweenness
#check Betweenness.commonNeighbors_complement
#print axioms Betweenness.commonNeighbors_complement
#check Betweenness.pole_lt_of_diameterTwo
#print axioms Betweenness.pole_lt_of_diameterTwo
#check Betweenness.not_close_compl_iff
#print axioms Betweenness.not_close_compl_iff
#check Betweenness.contribution_complement
#print axioms Betweenness.contribution_complement
#check Betweenness.betweenness_eq_nonclose
#print axioms Betweenness.betweenness_eq_nonclose
#check Betweenness.betweenness_eq_total_sub_co
#print axioms Betweenness.betweenness_eq_total_sub_co
#check Betweenness.uniform_iff_coUniform
#print axioms Betweenness.uniform_iff_coUniform
#check Betweenness.lowBUG_reduction
#print axioms Betweenness.lowBUG_reduction
#check Betweenness.weight_pos
#print axioms Betweenness.weight_pos
#check Betweenness.coBetweenness_lt_of_close_ssubset
#print axioms Betweenness.coBetweenness_lt_of_close_ssubset
#check Betweenness.lowBUG_close_not_ssubset
#print axioms Betweenness.lowBUG_close_not_ssubset
#check Betweenness.close_of_closeEdges_subset
#print axioms Betweenness.close_of_closeEdges_subset
#check Betweenness.lowBUG_component_of_leaf
#print axioms Betweenness.lowBUG_component_of_leaf
#check Betweenness.isolated_starComponent
#print axioms Betweenness.isolated_starComponent
#check Betweenness.lowBUG_component_of_degree_le_one
#print axioms Betweenness.lowBUG_component_of_degree_le_one
#check Betweenness.lowBUG_exists_degree_le_one
#print axioms Betweenness.lowBUG_exists_degree_le_one
#check Betweenness.lowBUG_exists_starComponent
#print axioms Betweenness.lowBUG_exists_starComponent
#check Betweenness.close_component_iff
#print axioms Betweenness.close_component_iff
#check Betweenness.weighted_double_count
#print axioms Betweenness.weighted_double_count
#check Betweenness.close_double_count
#print axioms Betweenness.close_double_count
#check Betweenness.co_double_count
#print axioms Betweenness.co_double_count
#check Betweenness.star_component_edge_count
#print axioms Betweenness.star_component_edge_count
#check Betweenness.star_edge_closeVertices
#print axioms Betweenness.star_edge_closeVertices
#check Betweenness.star_closeEdges
#print axioms Betweenness.star_closeEdges
#check Betweenness.star_coBetweenness
#print axioms Betweenness.star_coBetweenness
#check Betweenness.component_ncard_le
#print axioms Betweenness.component_ncard_le
#check Betweenness.star_size_lt_of_lowBUG
#print axioms Betweenness.star_size_lt_of_lowBUG
#check Betweenness.lowBUG_star_sizes_equal
#print axioms Betweenness.lowBUG_star_sizes_equal
#check Betweenness.star_component_reduction
#print axioms Betweenness.star_component_reduction
#check Betweenness.pairs_componentGraph
#print axioms Betweenness.pairs_componentGraph
#check Betweenness.component_degree_sum
#print axioms Betweenness.component_degree_sum
#check Betweenness.component_vertices_sum
#print axioms Betweenness.component_vertices_sum
#check Betweenness.component_edges_sum
#print axioms Betweenness.component_edges_sum
#check Betweenness.nonstar_component_edges_ge_vertices
#print axioms Betweenness.nonstar_component_edges_ge_vertices
#check Betweenness.exotic_star_count
#print axioms Betweenness.exotic_star_count
#check Betweenness.uniform_component_impossible
#print axioms Betweenness.uniform_component_impossible
#check Betweenness.closeEdges_eq_of_subset
#print axioms Betweenness.closeEdges_eq_of_subset
#check Betweenness.exotic_no_degree_two_triangle
#print axioms Betweenness.exotic_no_degree_two_triangle
#check Betweenness.pairs_incident_sum
#print axioms Betweenness.pairs_incident_sum
#check Betweenness.close_incidence_double
#print axioms Betweenness.close_incidence_double
#check Betweenness.exotic_min_degree
#print axioms Betweenness.exotic_min_degree
#check Betweenness.exotic_degree_close
#print axioms Betweenness.exotic_degree_close
#check Betweenness.exotic_pole_four
#print axioms Betweenness.exotic_pole_four
#check Betweenness.exotic_local_bounds
#print axioms Betweenness.exotic_local_bounds
#check Betweenness.closeEdges_subset_component
#print axioms Betweenness.closeEdges_subset_component
#check Betweenness.pole_le_degree_sum
#print axioms Betweenness.pole_le_degree_sum
#check Betweenness.edge_degree_excess_bound
#print axioms Betweenness.edge_degree_excess_bound
#check Betweenness.adjacent_close_pair
#print axioms Betweenness.adjacent_close_pair
#check LowBUG.small_vertex_bounds_impossible
#print axioms LowBUG.small_vertex_bounds_impossible
#check LowBUG.reciprocal_variance_identity
#print axioms LowBUG.reciprocal_variance_identity
#check LowBUG.average_bounds_impossible
#print axioms LowBUG.average_bounds_impossible
#check LowBUG.finite_inverse_jensen
#print axioms LowBUG.finite_inverse_jensen
#check LowBUG.reciprocal_equality_forces_poles
#print axioms LowBUG.reciprocal_equality_forces_poles
#check LowBUG.finite_reciprocal_upper
#print axioms LowBUG.finite_reciprocal_upper
#check LowBUG.low_closeness_impossible
#print axioms LowBUG.low_closeness_impossible
#check Betweenness.exotic_co_value
#print axioms Betweenness.exotic_co_value
#check Betweenness.exotic_n_gt_four
#print axioms Betweenness.exotic_n_gt_four
#check Betweenness.exotic_co_lower
#print axioms Betweenness.exotic_co_lower
#check Betweenness.exotic_star_size_ge_four
#print axioms Betweenness.exotic_star_size_ge_four
#check Betweenness.exotic_max_data
#print axioms Betweenness.exotic_max_data
#check Betweenness.exotic_closeness_lower
#print axioms Betweenness.exotic_closeness_lower
#check LowBUG.finite_average_obstruction
#print axioms LowBUG.finite_average_obstruction
#check Betweenness.component_average_obstruction
#print axioms Betweenness.component_average_obstruction
#check Betweenness.lowBUG_no_obstruction_component
#print axioms Betweenness.lowBUG_no_obstruction_component
#check Betweenness.counterexample_component_data
#print axioms Betweenness.counterexample_component_data
#check Betweenness.exotic_impossible
#print axioms Betweenness.exotic_impossible
#check Betweenness.lowBUG_complement_equal_stars
#print axioms Betweenness.lowBUG_complement_equal_stars
#check Betweenness.pathThree_diameterTwo
#print axioms Betweenness.pathThree_diameterTwo
#check Betweenness.pathThree_centre
#print axioms Betweenness.pathThree_centre
#check Betweenness.twoStars_compl_diameterTwo
#print axioms Betweenness.twoStars_compl_diameterTwo
#check Betweenness.twoStars_compl_betweenness
#print axioms Betweenness.twoStars_compl_betweenness
#check Betweenness.cycleFive_diameterTwo
#print axioms Betweenness.cycleFive_diameterTwo
#check Betweenness.cycleFive_betweenness
#print axioms Betweenness.cycleFive_betweenness
#check Betweenness.cycleFive_not_half
#print axioms Betweenness.cycleFive_not_half
#check Betweenness.disconnected_zero
#print axioms Betweenness.disconnected_zero
#check Betweenness.disconnected_not_connected
#print axioms Betweenness.disconnected_not_connected
#check Betweenness.disconnected_not_lowBUG
#print axioms Betweenness.disconnected_not_lowBUG
#check Betweenness.full_close_edge_guard
#print axioms Betweenness.full_close_edge_guard
#check Betweenness.mixedStars_supp_zero
#print axioms Betweenness.mixedStars_supp_zero
#check Betweenness.mixedStars_supp_one
#print axioms Betweenness.mixedStars_supp_one
#check Betweenness.mixedStars_not_equal
#print axioms Betweenness.mixedStars_not_equal
#check Betweenness.mixedStars_star_zero
#print axioms Betweenness.mixedStars_star_zero
#check Betweenness.mixedStars_star_one
#print axioms Betweenness.mixedStars_star_one
#check Betweenness.mixedStars_componentwise
#print axioms Betweenness.mixedStars_componentwise
#check Betweenness.complement_two_sizes_guard
#print axioms Betweenness.complement_two_sizes_guard
#check Betweenness.twoStars_compl_lowBUG
#print axioms Betweenness.twoStars_compl_lowBUG

#print Betweenness.sigma
#print Betweenness.sigmaThrough
#print Betweenness.betweenness
#print Betweenness.LowBUG
#print Betweenness.EqualStarUnion
#print Betweenness.StarComponent
#print Betweenness.ObstructionComponent
```


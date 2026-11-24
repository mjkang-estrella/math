# Lean source appendix (MathDB 350694)

All modules, in import order; each block is byte-identical to `src/<Module>.lean`.
The endpoint `BlowupBetweenness.hartman_pokorna_conj12_false` is in BlowupWitness.lean.

### `BlowupBetweennessDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Definitions for MathDB 350694 (Hartman–Pokorná, arXiv:2105.06777, Conjecture 12).

`sigma`, `sigmaThrough` and `betweenness` are copied verbatim from the accepted
MathDB 382260 packet (`BetweennessDefinitions.lean`), under a new namespace.
Source definition: B(x) = Σ_{{u,v} ⊆ V(G) \ {x}} σ_{u,v}(x) / σ_{u,v}, where σ_{u,v} is the
number of shortest u–v paths and σ_{u,v}(x) the number of those passing through x.
Shortest walks are paths (`shortest_isPath`); unordered pairs are the pairs v < w.

The blow-up G[H_1, …, H_n] (source p. 2): vertex set the disjoint union of the V(H_i),
edges E(H_i) inside each part and all edges between parts i ≠ j with v_i v_j ∈ E(G).
Here the vertex set is `Fin N`, `π : Fin N → Fin n` says which part a vertex lies in,
and H_i is the restriction of `H` to the fibre `π⁻¹(i)`; `H` matters only inside fibres.
-/

open scoped BigOperators
namespace BlowupBetweenness
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

lemma sigma_pos (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.Connected) (v w : Fin n) : 0 < sigma G v w := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v w
  exact Finset.card_pos.mpr ⟨p, SimpleGraph.mem_finsetWalkLength_iff.mpr hp⟩

lemma shortest_isPath (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v w : Fin n} {p : G.Walk v w}
    (hp : p ∈ G.finsetWalkLength (G.dist v w) v w) : p.IsPath :=
  p.isPath_of_length_eq_dist (SimpleGraph.mem_finsetWalkLength_iff.mp hp)

/-- The blow-up `G[H_1, …, H_n]`: `x ~ y` iff they lie in one part and are adjacent in
`H`, or they lie in parts `π x`, `π y` adjacent in `G`. -/
def blowUp {N : ℕ} (G : SimpleGraph (Fin n)) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) :
    SimpleGraph (Fin N) where
  Adj x y := (π x = π y ∧ H.Adj x y) ∨ G.Adj (π x) (π y)
  symm := ⟨fun x y h => by
    rcases h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨_, h⟩ | h
    · exact H.loopless.irrefl x h
    · exact G.loopless.irrefl _ h⟩

instance {N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Fin N → Fin n)
    (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] : DecidableRel (blowUp G π H).Adj :=
  fun x y => inferInstanceAs (Decidable ((π x = π y ∧ H.Adj x y) ∨ G.Adj (π x) (π y)))

/-- A vertex cut of size one: deleting `c` leaves a graph that is not connected. -/
def HasCutVertex (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c, ¬ (G.induce {v | v ≠ c}).Connected

/-- Betweenness-uniform: all vertices have the same betweenness. -/
def BetweennessUniform (X : SimpleGraph (Fin n)) [DecidableRel X.Adj] : Prop :=
  ∀ x y, betweenness X x = betweenness X y

/-- Conjecture 12 of Hartman–Pokorná (as recorded in MathDB 350694). -/
def Conjecture12 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → 3 ≤ G.diam → HasCutVertex G →
    ∀ (N : ℕ) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
      Function.Surjective π → ¬ BetweennessUniform (blowUp G π H)

/-- A cluster graph (disjoint union of cliques) given by a labelling. -/
def cluster {L : Type} (κ : Fin n → L) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ κ x = κ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {L : Type} [DecidableEq L] (κ : Fin n → L) : DecidableRel (cluster κ).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ κ x = κ y))

#print axioms sigma_pos
#print axioms shortest_isPath
end BlowupBetweenness
```

### `BlowupWalkCounting.lean`

```lean
import BlowupBetweennessDefinitions
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
General shortest-walk counting on a finite simple graph on `Fin n`:
a distance certificate, the first-step recursion for σ, symmetry, and the
splitting formula σ_{uv}(z) = [d(u,z)+d(z,v)=d(u,v)] σ_{uz} σ_{zv}.
-/

open scoped BigOperators
namespace BlowupBetweenness
open SimpleGraph
variable {n : ℕ}

section potential
variable (G : SimpleGraph (Fin n))

theorem le_length_of_potential (D : Fin n → Fin n → ℕ) (hD0 : ∀ i, D i i = 0)
    (hlip : ∀ i j k, G.Adj i k → D i j ≤ D k j + 1) :
    ∀ {u v : Fin n} (p : G.Walk u v), D u v ≤ p.length := by
  intro u v p
  induction p with
  | nil => simp [hD0]
  | cons h p ih =>
    rw [Walk.length_cons]
    exact (hlip _ _ _ h).trans (by omega)

theorem exists_walk_of_potential (D : Fin n → Fin n → ℕ) (hD0 : ∀ i, D i i = 0)
    (hdesc : ∀ i j, i ≠ j → ∃ k, G.Adj i k ∧ D k j + 1 = D i j) :
    ∀ (d : ℕ) (u v : Fin n), D u v = d → ∃ p : G.Walk u v, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro u v h
    by_cases huv : u = v
    · subst huv; exact ⟨Walk.nil, rfl⟩
    · obtain ⟨k, _, hk⟩ := hdesc u v huv; omega
  | succ d ih =>
    intro u v h
    by_cases huv : u = v
    · subst huv; rw [hD0] at h; omega
    · obtain ⟨k, hk, hkd⟩ := hdesc u v huv
      obtain ⟨q, hq⟩ := ih k v (by omega)
      exact ⟨Walk.cons hk q, by simp [hq]⟩

/-- A distance certificate: a table vanishing on the diagonal, 1-Lipschitz along
edges and with a descending neighbour is the graph distance. -/
theorem dist_eq_of_potential (D : Fin n → Fin n → ℕ) (hD0 : ∀ i, D i i = 0)
    (hlip : ∀ i j k, G.Adj i k → D i j ≤ D k j + 1)
    (hdesc : ∀ i j, i ≠ j → ∃ k, G.Adj i k ∧ D k j + 1 = D i j) (u v : Fin n) :
    G.Reachable u v ∧ G.dist u v = D u v := by
  obtain ⟨p, hp⟩ := exists_walk_of_potential G D hD0 hdesc _ u v rfl
  have hr : G.Reachable u v := ⟨p⟩
  refine ⟨hr, le_antisymm ?_ ?_⟩
  · exact hp ▸ G.dist_le p
  · obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    exact hq ▸ le_length_of_potential G D hD0 hlip q

end potential

section counting
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma card_walks_succ (k : ℕ) (u v : Fin n) :
    (G.finsetWalkLength (k + 1) u v).card =
      ∑ w, if G.Adj u w then (G.finsetWalkLength k w v).card else 0 := by
  have h1 := G.adjMatrix_pow_apply_eq_card_walk (α := ℕ) (k + 1) u v
  rw [card_set_walk_length_eq, Nat.cast_id] at h1
  rw [← h1, pow_succ', Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [adjMatrix_pow_apply_eq_card_walk, card_set_walk_length_eq, Nat.cast_id, adjMatrix_apply]
  split_ifs <;> simp

lemma card_walks_eq_zero_of_lt {k : ℕ} {u v : Fin n} (h : k < G.dist u v) :
    (G.finsetWalkLength k u v).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have := G.dist_le p
  rw [mem_finsetWalkLength_iff.mp hp] at this
  omega

/-- First-step recursion for the number of shortest walks. -/
theorem sigma_rec (hG : G.Connected) {u v : Fin n} (huv : u ≠ v) :
    sigma G u v = ∑ w, if G.Adj u w ∧ G.dist w v + 1 = G.dist u v then sigma G w v else 0 := by
  obtain ⟨k, hk⟩ : ∃ k, G.dist u v = k + 1 :=
    ⟨G.dist u v - 1, by have := hG.pos_dist_of_ne huv; omega⟩
  unfold sigma
  rw [hk, card_walks_succ]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : G.Adj u w
  · have htri : G.dist u v ≤ G.dist u w + G.dist w v := hG.dist_triangle
    rw [dist_eq_one_iff_adj.mpr hw] at htri
    by_cases hd : G.dist w v = k
    · simp [hw, hd]
    · have hc : ¬ (G.dist w v + 1 = k + 1) := fun h' => hd (by omega)
      simp only [hw, hc, true_and, ↓reduceIte]
      rw [card_walks_eq_zero_of_lt]
      omega
  · simp [hw]

lemma card_walks_symm (k : ℕ) (u v : Fin n) :
    (G.finsetWalkLength k u v).card = (G.finsetWalkLength k v u).card := by
  apply Finset.card_bij (fun p _ => p.reverse)
  · intro p hp
    simpa [mem_finsetWalkLength_iff] using hp
  · intro p _ q _ h
    simpa using congrArg Walk.reverse h
  · intro q hq
    exact ⟨q.reverse, by simpa [mem_finsetWalkLength_iff] using hq, by simp⟩

lemma sigma_symm (u v : Fin n) : sigma G u v = sigma G v u := by
  unfold sigma
  rw [dist_comm]
  exact card_walks_symm G _ u v

lemma sigmaThrough_symm (u v x : Fin n) : sigmaThrough G u v x = sigmaThrough G v u x := by
  unfold sigmaThrough
  rw [dist_comm]
  apply Finset.card_bij (fun p _ => p.reverse)
  · intro p hp
    simp only [Finset.mem_filter, mem_finsetWalkLength_iff, Walk.length_reverse,
      Walk.support_reverse, List.mem_reverse] at hp ⊢
    tauto
  · intro p _ q _ h
    simpa using congrArg Walk.reverse h
  · intro q hq
    refine ⟨q.reverse, ?_, by simp⟩
    simp only [Finset.mem_filter, mem_finsetWalkLength_iff, Walk.length_reverse,
      Walk.support_reverse, List.mem_reverse] at hq ⊢
    tauto

omit [DecidableRel G.Adj] in
lemma append_inj_of_length :
    ∀ {u w v : Fin n} (p p' : G.Walk u w) (q q' : G.Walk w v),
      p.length = p'.length → p.append q = p'.append q' → p = p' ∧ q = q' := by
  intro u w v p
  induction p with
  | nil =>
    intro p' q q' hl h
    cases p' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons _ _ => simp at hl
  | cons ha p ih =>
    intro p' q q' hl h
    cases p' with
    | nil => simp at hl
    | cons hb p' =>
      simp only [Walk.cons_append] at h
      injection h with h1 h2 h3 h4
      subst h2
      have h2 := eq_of_heq h4
      obtain ⟨rfl, rfl⟩ := ih p' q q' (by simpa using hl) h2
      exact ⟨rfl, rfl⟩

lemma sigmaThrough_left (u v : Fin n) : sigmaThrough G u v u = 0 := by
  unfold sigmaThrough
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  exact h.2.1 rfl

lemma sigmaThrough_right (u v : Fin n) : sigmaThrough G u v v = 0 := by
  unfold sigmaThrough
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  exact h.2.2 rfl

/-- Splitting a shortest walk at an inner vertex. -/
theorem sigmaThrough_eq (hG : G.Connected) {u v z : Fin n} (hu : z ≠ u) (hv : z ≠ v) :
    sigmaThrough G u v z =
      if G.dist u z + G.dist z v = G.dist u v then sigma G u z * sigma G z v else 0 := by
  have key : ∀ p ∈ G.finsetWalkLength (G.dist u v) u v, ∀ hz : z ∈ p.support,
      (p.takeUntil z hz).length = G.dist u z ∧ (p.dropUntil z hz).length = G.dist z v ∧
        G.dist u z + G.dist z v = G.dist u v := by
    intro p hp hz
    have hl := mem_finsetWalkLength_iff.mp hp
    have hs := congrArg Walk.length (p.take_spec hz)
    rw [Walk.length_append] at hs
    have h1 := G.dist_le (p.takeUntil z hz)
    have h2 := G.dist_le (p.dropUntil z hz)
    have h3 : G.dist u v ≤ G.dist u z + G.dist z v := hG.dist_triangle
    omega
  unfold sigmaThrough
  split_ifs with h
  · have hS : (G.finsetWalkLength (G.dist u v) u v).filter
          (fun p => z ∈ p.support ∧ z ≠ u ∧ z ≠ v) =
        ((G.finsetWalkLength (G.dist u z) u z) ×ˢ (G.finsetWalkLength (G.dist z v) z v)).image
          (fun pq => pq.1.append pq.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Prod.exists]
      constructor
      · rintro ⟨hp, hz, -, -⟩
        obtain ⟨h1, h2, -⟩ := key p hp hz
        exact ⟨p.takeUntil z hz, p.dropUntil z hz,
          ⟨mem_finsetWalkLength_iff.mpr h1, mem_finsetWalkLength_iff.mpr h2⟩, p.take_spec hz⟩
      · rintro ⟨q1, q2, ⟨h1, h2⟩, rfl⟩
        rw [mem_finsetWalkLength_iff] at h1 h2
        refine ⟨mem_finsetWalkLength_iff.mpr (by rw [Walk.length_append]; omega), ?_, hu, hv⟩
        rw [Walk.mem_support_append_iff]
        exact Or.inl q1.end_mem_support
    rw [hS, Finset.card_image_of_injOn, Finset.card_product]
    · rfl
    · rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
        mem_finsetWalkLength_iff] at hp hq
      obtain ⟨rfl, rfl⟩ := append_inj_of_length G p1 q1 p2 q2 (hp.1.trans hq.1.symm) heq
      rfl
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p hp ⟨hz, -, -⟩
    exact h (key p hp hz).2.2

/-- Betweenness as half the sum over ordered pairs, in split form. -/
theorem betweenness_eq_half (hG : G.Connected) (x : Fin n) :
    betweenness G x = (1 / 2) * ∑ u, ∑ v,
      (if u ≠ v ∧ u ≠ x ∧ v ≠ x ∧ G.dist u x + G.dist x v = G.dist u v then
        ((sigma G u x * sigma G x v : ℕ) : ℚ) / sigma G u v else 0) := by
  set f : Fin n → Fin n → ℚ := fun u v => (sigmaThrough G u v x : ℚ) / sigma G u v with hf
  have hsymm : ∀ u v, f u v = f v u := by
    intro u v; simp only [hf, sigmaThrough_symm G u v x, sigma_symm G u v]
  have h1 : (∑ u, ∑ v, if u < v then f u v else 0) = ∑ u, ∑ v, if v < u then f u v else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hsymm]
  have h2 : (∑ u, ∑ v, if u ≠ v then f u v else 0) =
      (∑ u, ∑ v, if u < v then f u v else 0) + ∑ u, ∑ v, if v < u then f u v else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rcases lt_trichotomy u v with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have h3 : ∀ u v, (if u ≠ v then f u v else 0) =
      (if u ≠ v ∧ u ≠ x ∧ v ≠ x ∧ G.dist u x + G.dist x v = G.dist u v then
        ((sigma G u x * sigma G x v : ℕ) : ℚ) / sigma G u v else 0) := by
    intro u v
    by_cases huv : u = v
    · simp [huv]
    by_cases hxu : x = u
    · subst hxu; simp [hf, sigmaThrough_left]
    by_cases hxv : x = v
    · subst hxv; simp [hf, sigmaThrough_right]
    simp only [hf, sigmaThrough_eq G hG hxu hxv]
    by_cases hd : G.dist u x + G.dist x v = G.dist u v
    · simp [huv, Ne.symm hxu, Ne.symm hxv, hd]
    · simp [hd]
  have hB : betweenness G x = ∑ u, ∑ v, if u < v then f u v else 0 := rfl
  rw [hB]
  simp_rw [← h3]
  rw [h2, ← h1]
  ring

end counting

#print axioms dist_eq_of_potential
#print axioms sigma_rec
#print axioms sigmaThrough_eq
#print axioms betweenness_eq_half
end BlowupBetweenness
```

### `BlowupCluster.lean`

```lean
import BlowupWalkCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
Blow-ups of a base graph by cluster graphs (every `H_i` a disjoint union of cliques).
Distances, shortest-walk counts and betweenness are computed from a base distance
certificate `D` and a base weighted walk-count certificate `F` (the lifting lemma in
recursive form: shortest walks between different parts project to base geodesics and
choose one vertex in every inner part).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
open SimpleGraph
variable {n N : ℕ}

lemma ite_true_of {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

lemma ite_false_of {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

/-- Number of vertices in the part `i`. -/
def fibreCard (π : Fin N → Fin n) (i : Fin n) : ℕ := (Finset.univ.filter (fun x => π x = i)).card

lemma sum_comp_fibre {R : Type} [CommSemiring R] (π : Fin N → Fin n) (g : Fin n → R) :
    ∑ x, g (π x) = ∑ i, (fibreCard π i : R) * g i := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => g (π x))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g i) (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, nsmul_eq_mul, fibreCard]

/-- Base distance certificate together with "every vertex has a neighbour". -/
structure BaseCert (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → ℕ) : Prop where
  zero : ∀ i, D i i = 0
  lip : ∀ i j k, G.Adj i k → D i j ≤ D k j + 1
  desc : ∀ i j, i ≠ j → ∃ k, G.Adj i k ∧ D k j + 1 = D i j
  nbr : ∀ i, ∃ j, G.Adj i j

section cert
variable {G : SimpleGraph (Fin n)} {D : Fin n → Fin n → ℕ}

lemma BaseCert.pos (hc : BaseCert G D) {i j : Fin n} (h : i ≠ j) : 1 ≤ D i j := by
  obtain ⟨k, _, hk⟩ := hc.desc i j h; omega

lemma BaseCert.eq_zero_iff (hc : BaseCert G D) {i j : Fin n} : D i j = 0 ↔ i = j := by
  constructor
  · intro h; by_contra h'; have := hc.pos h'; omega
  · rintro rfl; exact hc.zero i

lemma BaseCert.one_iff (hc : BaseCert G D) {i j : Fin n} : D i j = 1 ↔ G.Adj i j := by
  constructor
  · intro h
    have hij : i ≠ j := by rintro rfl; rw [hc.zero] at h; omega
    obtain ⟨k, hk, hkd⟩ := hc.desc i j hij
    have : D k j = 0 := by omega
    rw [hc.eq_zero_iff] at this
    exact this ▸ hk
  · intro h
    have h1 := hc.lip i j j h
    rw [hc.zero] at h1
    have := hc.pos h.ne
    omega

end cert

section blowup
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Fin N → Fin n)
  {L : Type} [DecidableEq L] (κ : Fin N → L) (D : Fin n → Fin n → ℕ)

/-- Distance table of the blow-up. -/
def distX (x y : Fin N) : ℕ :=
  if π x = π y then (if x = y then 0 else if κ x = κ y then 1 else 2) else D (π x) (π y)

omit [DecidableRel G.Adj] [DecidableEq L] in
lemma adjX_iff {x y : Fin N} :
    (blowUp G π (cluster κ)).Adj x y ↔ (π x = π y ∧ x ≠ y ∧ κ x = κ y) ∨ G.Adj (π x) (π y) :=
  Iff.rfl

variable {G π κ D}

lemma distX_cert (hc : BaseCert G D) (hπ : Function.Surjective π) (x y : Fin N) :
    (blowUp G π (cluster κ)).Reachable x y ∧
      (blowUp G π (cluster κ)).dist x y = distX π κ D x y := by
  apply dist_eq_of_potential
  · intro x; simp [distX]
  · intro x y w hxw
    rw [adjX_iff] at hxw
    rcases hxw with ⟨h1, h2, h3⟩ | h
    · by_cases hy : π x = π y
      · have hwy : π w = π y := h1 ▸ hy
        by_cases hw : w = y
        · subst hw
          simp [distX, h1, h2, h3]
        · simp only [distX, hy, hwy, hw, eq_self_iff_true, ↓reduceIte]
          split_ifs <;> omega
      · have hwy : ¬ π w = π y := h1 ▸ hy
        simp only [distX, hy, hwy, h1, ↓reduceIte]
        omega
    · have hxw : π x ≠ π w := G.ne_of_adj h
      by_cases hy : π x = π y
      · have hwy : ¬ π w = π y := fun e => hxw (hy.trans e.symm)
        have := hc.pos hwy
        simp only [distX, hy, hwy, eq_self_iff_true, ↓reduceIte]
        split_ifs <;> omega
      · by_cases hwy : π w = π y
        · have h1 := hc.lip (π x) (π w) (π w) h
          rw [hc.zero] at h1
          simp only [distX, hy, hwy, ↓reduceIte]
          rw [← hwy]
          split_ifs <;> omega
        · simp only [distX, hy, hwy, ↓reduceIte]
          exact hc.lip _ _ _ h
  · intro x y hxy
    by_cases hy : π x = π y
    · by_cases hk : κ x = κ y
      · refine ⟨y, Or.inl ⟨hy, hxy, hk⟩, ?_⟩
        simp [distX, hy, hxy, hk]
      · obtain ⟨j, hj⟩ := hc.nbr (π x)
        obtain ⟨w, rfl⟩ := hπ j
        refine ⟨w, Or.inr hj, ?_⟩
        have hwy : ¬ π w = π y := fun e => G.ne_of_adj hj (hy.trans e.symm)
        have h1 : D (π w) (π y) = 1 := hy ▸ (hc.one_iff).mpr hj.symm
        simp only [distX, hy, hwy, hxy, hk, h1, ↓reduceIte]
    · obtain ⟨k, hk, hkd⟩ := hc.desc (π x) (π y) hy
      by_cases hky : k = π y
      · subst hky
        refine ⟨y, Or.inr hk, ?_⟩
        rw [hc.zero] at hkd
        simp only [distX, hy, ↓reduceIte]
        omega
      · obtain ⟨w, rfl⟩ := hπ k
        refine ⟨w, Or.inr hk, ?_⟩
        simp only [distX, hy, hky, ↓reduceIte]
        omega

lemma connectedX (hc : BaseCert G D) (hπ : Function.Surjective π) [Nonempty (Fin N)] :
    (blowUp G π (cluster κ)).Connected :=
  ⟨fun x y => (distX_cert hc hπ x y).1⟩

end blowup

section sigma
variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma sigma_self (u : Fin n) : sigma G u u = 1 := by
  simp [sigma, SimpleGraph.finsetWalkLength]

lemma sigma_adj {u v : Fin n} (h : G.Adj u v) : sigma G u v = 1 := by
  unfold sigma
  rw [dist_eq_one_iff_adj.mpr h, card_walks_succ]
  rw [Finset.sum_eq_single v]
  · simp [h, SimpleGraph.finsetWalkLength]
  · intro w _ hw
    split_ifs
    · simp [SimpleGraph.finsetWalkLength, hw]
    · rfl
  · simp

end sigma

#print axioms distX_cert
#print axioms sigma_adj

section formula
variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {π : Fin N → Fin n}
  {L : Type} [DecidableEq L] {κ : Fin N → L} {D : Fin n → Fin n → ℕ}

/-- Sum of the part sizes over the neighbours of `i` in the base. -/
def nbrWeight (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Fin N → Fin n) (i : Fin n) : ℕ :=
  ∑ k, if G.Adj i k then fibreCard π k else 0

/-- Ordered pairs of vertices of part `i` lying in different cliques. -/
def crossPairs (π : Fin N → Fin n) (κ : Fin N → L) (i : Fin n) : ℕ :=
  ∑ u, ∑ v, if π u = i ∧ π v = i ∧ κ u ≠ κ v then 1 else 0

/-- The weighted walk-count certificate on the base. -/
def FCert (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Fin N → Fin n)
    (D F : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → F i j = if D i j = 1 then 1 else
    ∑ k, if G.Adj i k ∧ D k j + 1 = D i j then fibreCard π k * F k j else 0

/-- Pair-dependency of a base vertex `k` for base endpoints `i`, `j`. -/
def pairDep (D F : Fin n → Fin n → ℕ) (i j k : Fin n) : ℚ :=
  if D i k + D k j = D i j then ((F i k * F k j : ℕ) : ℚ) / (F i j : ℚ) else 0

lemma distX_eq_zero_iff (hc : BaseCert G D) {x y : Fin N} : distX π κ D x y = 0 ↔ x = y := by
  unfold distX
  by_cases h : π x = π y
  · simp only [h, ↓reduceIte]; split_ifs <;> simp_all
  · simp only [h, ↓reduceIte, hc.eq_zero_iff]
    exact ⟨False.elim, fun e => h (congrArg π e)⟩

theorem sigmaX_cross (hc : BaseCert G D) (hπ : Function.Surjective π) {F : Fin n → Fin n → ℕ}
    (hF : FCert G π D F) :
    ∀ d (x y : Fin N), D (π x) (π y) = d → π x ≠ π y →
      sigma (blowUp G π (cluster κ)) x y = F (π x) (π y) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x y hd hxy
  have : Nonempty (Fin N) := ⟨x⟩
  have hconn := connectedX (κ := κ) hc hπ
  have hdist : ∀ a b, (blowUp G π (cluster κ)).dist a b = distX π κ D a b :=
    fun a b => (distX_cert hc hπ a b).2
  have hne : x ≠ y := fun e => hxy (congrArg π e)
  rw [sigma_rec _ hconn hne]
  simp only [hdist]
  have hxyd : distX π κ D x y = d := by simp [distX, hxy, hd]
  rw [hxyd, hF _ _ hxy, hd]
  by_cases h1 : d = 1
  · subst h1
    rw [ite_true_of (rfl : (1 : ℕ) = 1), Finset.sum_eq_single y]
    · have hadj : G.Adj (π x) (π y) := hc.one_iff.mp hd
      have : distX π κ D y y = 0 := (distX_eq_zero_iff hc).mpr rfl
      simp [this, adjX_iff, hadj, sigma_self]
    · intro w _ hwy
      have : distX π κ D w y ≠ 0 := fun e => hwy ((distX_eq_zero_iff hc).mp e)
      rw [ite_false_of (by omega)]
    · simp
  · rw [ite_false_of h1]
    have hd2 : 2 ≤ d := by have := hc.pos hxy; omega
    have key : ∀ w, (if (blowUp G π (cluster κ)).Adj x w ∧ distX π κ D w y + 1 = d then
        sigma (blowUp G π (cluster κ)) w y else 0) =
        (fun k => if G.Adj (π x) k ∧ D k (π y) + 1 = d then F k (π y) else 0) (π w) := by
      intro w
      by_cases hwx : π w = π x
      · have : distX π κ D w y = d := by simp [distX, hwx, hxy, hd]
        have hn : ¬ G.Adj (π x) (π w) := by rw [hwx]; exact G.loopless.irrefl _
        simp [this, hn]
      by_cases hwy : π w = π y
      · have hn : ¬ G.Adj (π x) (π w) := by
          rw [hwy, ← hc.one_iff, hd]; omega
        have hadj : ¬ (blowUp G π (cluster κ)).Adj x w := by
          rw [adjX_iff]; rintro (⟨h, -⟩ | h)
          · exact hwx h.symm
          · exact hn h
        simp [hadj, hn]
      · have hadj : (blowUp G π (cluster κ)).Adj x w ↔ G.Adj (π x) (π w) := by
          rw [adjX_iff]
          constructor
          · rintro (⟨h, -⟩ | h)
            · exact absurd h.symm hwx
            · exact h
          · exact Or.inr
        have hdw : distX π κ D w y = D (π w) (π y) := by simp [distX, hwy]
        simp only [hadj, hdw]
        split_ifs with hcnd
        · exact ih _ (by omega) w y rfl hwy
        · rfl
    rw [Finset.sum_congr rfl (fun w _ => key w)]
    refine (sum_comp_fibre (R := ℕ) π (fun k => if G.Adj (π x) k ∧ D k (π y) + 1 = d then F k (π y) else 0)).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

theorem sigmaX_same (hc : BaseCert G D) (hπ : Function.Surjective π) {x y : Fin N}
    (h : π x = π y) (hk : κ x ≠ κ y) :
    sigma (blowUp G π (cluster κ)) x y = nbrWeight G π (π x) := by
  have : Nonempty (Fin N) := ⟨x⟩
  have hconn := connectedX (κ := κ) hc hπ
  have hdist : ∀ a b, (blowUp G π (cluster κ)).dist a b = distX π κ D a b :=
    fun a b => (distX_cert hc hπ a b).2
  have hne : x ≠ y := fun e => hk (congrArg κ e)
  rw [sigma_rec _ hconn hne]
  simp only [hdist]
  have hxyd : distX π κ D x y = 2 := by simp [distX, h, hne, hk]
  rw [hxyd]
  have key : ∀ w, (if (blowUp G π (cluster κ)).Adj x w ∧ distX π κ D w y + 1 = 2 then
      sigma (blowUp G π (cluster κ)) w y else 0) =
      (fun k => if G.Adj (π x) k then 1 else 0) (π w) := by
    intro w
    by_cases hwx : π w = π x
    · have hn : ¬ G.Adj (π x) (π w) := by rw [hwx]; exact G.loopless.irrefl _
      have : ¬ ((blowUp G π (cluster κ)).Adj x w ∧ distX π κ D w y + 1 = 2) := by
        rintro ⟨ha, hd⟩
        rw [adjX_iff] at ha
        rcases ha with ⟨-, -, hxw⟩ | ha
        · have hwy : π w = π y := hwx.trans h
          unfold distX at hd
          simp only [hwy, ↓reduceIte] at hd
          split_ifs at hd with h1 h2
          · omega
          · exact hk (hxw.trans h2)
          · omega
        · exact hn ha
      rw [ite_false_of this]
      simp [hn]
    · have hwy : ¬ π w = π y := fun e => hwx (e.trans h.symm)
      have hadj : (blowUp G π (cluster κ)).Adj x w ↔ G.Adj (π x) (π w) := by
        rw [adjX_iff]
        constructor
        · rintro (⟨h', -⟩ | h')
          · exact absurd h'.symm hwx
          · exact h'
        · exact Or.inr
      have hdw : distX π κ D w y = D (π w) (π x) := by simp [distX, hwy, h]
      simp only [hadj, hdw]
      by_cases ha : G.Adj (π x) (π w)
      · have h1 : D (π w) (π x) = 1 := hc.one_iff.mpr ha.symm
        have hwy' : (blowUp G π (cluster κ)).Adj w y := by
          rw [adjX_iff]; right; rw [← h]; exact ha.symm
        simp [ha, h1, sigma_adj hwy']
      · simp [ha]
  rw [Finset.sum_congr rfl (fun w _ => key w), nbrWeight]
  refine (sum_comp_fibre (R := ℕ) π (fun k => if G.Adj (π x) k then 1 else 0)).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

end formula

#print axioms sigmaX_cross
#print axioms sigmaX_same
end BlowupBetweenness
```

### `BlowupFormula.lean`

```lean
import BlowupCluster
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
The betweenness of a vertex of a cluster blow-up, as a sum over base vertices
(the proof's formula: global pairs through the part of `z`, plus local pairs of the
neighbouring parts that lie in different cliques).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
open SimpleGraph
variable {n N : ℕ}
variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {π : Fin N → Fin n}
  {L : Type} [DecidableEq L] {κ : Fin N → L} {D : Fin n → Fin n → ℕ}

lemma distX_same {a b : Fin N} (h : π a = π b) (hab : a ≠ b) :
    distX π κ D a b = if κ a = κ b then 1 else 2 := by
  simp [distX, h, hab]

lemma distX_diff {a b : Fin N} (h : π a ≠ π b) : distX π κ D a b = D (π a) (π b) := by
  simp [distX, h]

theorem summand_eq (hc : BaseCert G D) (hπ : Function.Surjective π) {F : Fin n → Fin n → ℕ}
    (hF : FCert G π D F) (z u v : Fin N) :
    (if u ≠ v ∧ u ≠ z ∧ v ≠ z ∧ distX π κ D u z + distX π κ D z v = distX π κ D u v then
      ((sigma (blowUp G π (cluster κ)) u z * sigma (blowUp G π (cluster κ)) z v : ℕ) : ℚ) /
        sigma (blowUp G π (cluster κ)) u v else 0) =
      (if π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z then pairDep D F (π u) (π v) (π z) else 0) +
      (if π u = π v ∧ G.Adj (π u) (π z) ∧ κ u ≠ κ v then 1 / (nbrWeight G π (π u) : ℚ) else 0) := by
  by_cases huv : π u = π v
  · have hA : ¬ (π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z) := fun h => h.1 huv
    rw [ite_false_of hA, zero_add]
    by_cases hue : u = v
    · subst hue; simp
    by_cases hk : π u = π z
    · have hB : ¬ (π u = π v ∧ G.Adj (π u) (π z) ∧ κ u ≠ κ v) := by
        rintro ⟨-, h, -⟩; rw [hk] at h; exact G.loopless.irrefl _ h
      rw [ite_false_of hB]
      apply ite_false_of
      rintro ⟨-, huz, hvz, hd⟩
      rw [distX_same hk huz, distX_same (hk.symm.trans huv) (Ne.symm hvz),
        distX_same huv hue] at hd
      split_ifs at hd <;> simp_all
    · have hvz : π v ≠ π z := huv ▸ hk
      have hu' : u ≠ z := fun e => hk (congrArg π e)
      have hv' : v ≠ z := fun e => hvz (congrArg π e)
      rw [distX_diff hk, distX_diff (Ne.symm hvz), distX_same huv hue, ← huv]
      by_cases hadj : G.Adj (π u) (π z)
      · have h1 : D (π u) (π z) = 1 := hc.one_iff.mpr hadj
        have h2 : D (π z) (π u) = 1 := hc.one_iff.mpr hadj.symm
        rw [h1, h2]
        by_cases hκ : κ u = κ v
        · simp [hκ]
        · have s1 : sigma (blowUp G π (cluster κ)) u z = 1 := sigma_adj (Or.inr hadj)
          have s2 : sigma (blowUp G π (cluster κ)) z v = 1 :=
            sigma_adj (Or.inr (huv ▸ hadj.symm))
          have s3 := sigmaX_same hc hπ huv hκ
          simp [hκ, hue, hu', hv', s1, s2, s3, hadj]
      · have h1 : 2 ≤ D (π u) (π z) := by
          have := hc.pos hk; have := mt hc.one_iff.mp hadj; omega
        have hB : ¬ (π u = π u ∧ G.Adj (π u) (π z) ∧ κ u ≠ κ v) := fun h => hadj h.2.1
        rw [ite_false_of hB]
        apply ite_false_of
        rintro ⟨-, -, -, hd⟩
        have h3 : 1 ≤ D (π z) (π u) := hc.pos (Ne.symm hk)
        by_cases hκ : κ u = κ v
        · simp only [hκ, ↓reduceIte] at hd; omega
        · simp only [hκ, ↓reduceIte] at hd; omega
  · have hB : ¬ (π u = π v ∧ G.Adj (π u) (π z) ∧ κ u ≠ κ v) := fun h => huv h.1
    rw [ite_false_of hB, add_zero]
    by_cases hu : π u = π z
    · have hA : ¬ (π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z) := fun h => h.2.1 hu
      rw [ite_false_of hA]
      apply ite_false_of
      rintro ⟨-, huz, -, hd⟩
      have hzv : π z ≠ π v := hu ▸ huv
      rw [distX_diff hzv, distX_diff huv, ← hu] at hd
      have : distX π κ D u z ≠ 0 := fun e => huz ((distX_eq_zero_iff hc).mp e)
      omega
    by_cases hv : π v = π z
    · have hA : ¬ (π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z) := fun h => h.2.2 hv
      rw [ite_false_of hA]
      apply ite_false_of
      rintro ⟨-, -, hvz, hd⟩
      rw [distX_diff hu, distX_diff huv, hv] at hd
      have : distX π κ D z v ≠ 0 := fun e => hvz ((distX_eq_zero_iff hc).mp e).symm
      omega
    · have hA : π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z := ⟨huv, hu, hv⟩
      rw [ite_true_of hA]
      have hne : u ≠ v := fun e => huv (congrArg π e)
      have hu' : u ≠ z := fun e => hu (congrArg π e)
      have hv' : v ≠ z := fun e => hv (congrArg π e)
      rw [distX_diff hu, distX_diff (Ne.symm hv), distX_diff huv,
        sigmaX_cross hc hπ hF _ u z rfl hu, sigmaX_cross hc hπ hF _ z v rfl (Ne.symm hv),
        sigmaX_cross hc hπ hF _ u v rfl huv]
      simp only [pairDep, hne, hu', hv', ne_eq, not_false_eq_true, true_and]

/-- **Betweenness of a cluster blow-up.** -/
theorem betweenness_blowUp_cluster (hc : BaseCert G D) (hπ : Function.Surjective π)
    {F : Fin n → Fin n → ℕ} (hF : FCert G π D F) (z : Fin N) :
    betweenness (blowUp G π (cluster κ)) z = (1 / 2) *
      ((∑ i, ∑ j, if i ≠ j ∧ i ≠ π z ∧ j ≠ π z then
          ((fibreCard π i * fibreCard π j : ℕ) : ℚ) * pairDep D F i j (π z) else 0) +
        ∑ i, if G.Adj i (π z) then (crossPairs π κ i : ℚ) / nbrWeight G π i else 0) := by
  have : Nonempty (Fin N) := ⟨z⟩
  have hconn := connectedX (κ := κ) hc hπ
  have hdist : ∀ a b, (blowUp G π (cluster κ)).dist a b = distX π κ D a b :=
    fun a b => (distX_cert hc hπ a b).2
  rw [betweenness_eq_half _ hconn z]
  congr 1
  simp only [hdist]
  simp_rw [summand_eq hc hπ hF z, Finset.sum_add_distrib]
  congr 1
  · -- global pairs
    set a : Fin n → Fin n → ℚ := fun i j =>
      if i ≠ j ∧ i ≠ π z ∧ j ≠ π z then pairDep D F i j (π z) else 0 with ha
    have h1 : ∀ u, (∑ v, if π u ≠ π v ∧ π u ≠ π z ∧ π v ≠ π z then
        pairDep D F (π u) (π v) (π z) else 0) = ∑ j, (fibreCard π j : ℚ) * a (π u) j :=
      fun u => sum_comp_fibre (R := ℚ) π (a (π u))
    simp_rw [h1]
    rw [sum_comp_fibre (R := ℚ) π (fun i => ∑ j, (fibreCard π j : ℚ) * a i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha]
    split_ifs <;> push_cast <;> ring
  · -- local pairs
    have h2 : ∀ i, (if G.Adj i (π z) then (crossPairs π κ i : ℚ) / nbrWeight G π i else 0) =
        ∑ u, ∑ v, if G.Adj i (π z) ∧ π u = i ∧ π v = i ∧ κ u ≠ κ v then
          1 / (nbrWeight G π i : ℚ) else 0 := by
      intro i
      by_cases hi : G.Adj i (π z)
      · simp only [hi, true_and, ↓reduceIte, crossPairs]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      · simp [hi]
    simp_rw [h2]
    rw [eq_comm, Finset.sum_comm (f := fun i u => ∑ v, (if G.Adj i (π z) ∧ π u = i ∧ π v = i ∧
      κ u ≠ κ v then 1 / (nbrWeight G π i : ℚ) else 0))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm (f := fun i v => (if G.Adj i (π z) ∧ π u = i ∧ π v = i ∧
      κ u ≠ κ v then 1 / (nbrWeight G π i : ℚ) else 0))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (π u)]
    · by_cases h : π u = π v
      · simp [h]
      · have : ¬ (π v = π u) := fun e => h e.symm
        simp [h, this]
    · intro i _ hi
      exact ite_false_of (fun h => hi h.2.1.symm)
    · simp

#print axioms betweenness_blowUp_cluster
end BlowupBetweenness
```

### `BlowupClasses.lean`

```lean
import BlowupFormula
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
Vertex sets built from clique classes: `Fin (∑ c, sz c)`, read through `finSigmaFinEquiv`.
Class `c` has `sz c` vertices, all in base part `bf c`; the cluster label of a vertex is its
class, so each class is a clique of the blow-up and distinct classes of one part are
non-adjacent. Sums over vertices become sums over classes (no enumeration of vertices).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
variable {n C : ℕ} (sz : Fin C → ℕ) (bf : Fin C → Fin n)

/-- The class of a vertex. -/
def classOf (x : Fin (∑ c, sz c)) : Fin C := (finSigmaFinEquiv.symm x).1

/-- The part of a vertex. -/
def partOf (x : Fin (∑ c, sz c)) : Fin n := bf (classOf sz x)

lemma sum_classOf {R : Type} [CommSemiring R] (f : Fin C → R) :
    ∑ x : Fin (∑ c, sz c), f (classOf sz x) = ∑ c, (sz c : R) * f c := by
  have h := Equiv.sum_comp (finSigmaFinEquiv (n := sz)).symm
    (fun p : (c : Fin C) × Fin (sz c) => f p.1)
  rw [show (∑ x : Fin (∑ c, sz c), f (classOf sz x)) = _ from h, Fintype.sum_sigma]
  simp [Finset.sum_const, nsmul_eq_mul]

lemma fibreCard_partOf (i : Fin n) :
    fibreCard (partOf sz bf) i = ∑ c, sz c * (if bf c = i then 1 else 0) := by
  rw [fibreCard, Finset.card_filter]
  exact sum_classOf (R := ℕ) sz (fun c => if bf c = i then 1 else 0)

lemma crossPairs_partOf (i : Fin n) :
    crossPairs (partOf sz bf) (classOf sz) i =
      ∑ c, ∑ c', sz c * (sz c' * (if bf c = i ∧ bf c' = i ∧ c ≠ c' then 1 else 0)) := by
  unfold crossPairs partOf
  have h1 : ∀ u : Fin (∑ c, sz c), (∑ v : Fin (∑ c, sz c),
      if bf (classOf sz u) = i ∧ bf (classOf sz v) = i ∧ classOf sz u ≠ classOf sz v then 1 else 0)
      = ∑ c', sz c' * (if bf (classOf sz u) = i ∧ bf c' = i ∧ classOf sz u ≠ c' then 1 else 0) :=
    fun u => sum_classOf (R := ℕ) sz
      (fun c' => if bf (classOf sz u) = i ∧ bf c' = i ∧ classOf sz u ≠ c' then 1 else 0)
  simp_rw [h1]
  rw [sum_classOf (R := ℕ) sz
    (fun c => ∑ c', sz c' * (if bf c = i ∧ bf c' = i ∧ c ≠ c' then 1 else 0))]
  simp only [Nat.cast_id, Finset.mul_sum]

lemma partOf_mk (c : Fin C) (j : Fin (sz c)) :
    partOf sz bf (finSigmaFinEquiv ⟨c, j⟩) = bf c := by
  simp [partOf, classOf]

lemma partOf_surjective (pick : Fin n → Fin C) (hpick : ∀ i, bf (pick i) = i ∧ 0 < sz (pick i)) :
    Function.Surjective (partOf sz bf) := by
  intro i
  exact ⟨finSigmaFinEquiv ⟨pick i, ⟨0, (hpick i).2⟩⟩, by rw [partOf_mk, (hpick i).1]⟩

#print axioms sum_classOf
#print axioms crossPairs_partOf
end BlowupBetweenness
```

### `BlowupWedgeBase.lean`

```lean
import BlowupClasses
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
The base graph: two 5-cycles `0-1-2-3-4-0` and `0-5-6-7-8-0` sharing the vertex `0`
(in the proof's names: c = 0, A₁ B₁ D₁ E₁ = 1 2 3 4, A₂ B₂ D₂ E₂ = 5 6 7 8).
Its distance table, connectivity, diameter 4, the cut vertex 0, the weighted
geodesic counts, and the betweenness of any cluster blow-up of it.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
namespace Wedge
open SimpleGraph

/-- The ten edges of the wedge of two 5-cycles. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 7), (7, 8), (8, 0)]

def base : SimpleGraph (Fin 9) where
  Adj i j := (i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel base.Adj :=
  fun i j => inferInstanceAs (Decidable ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges))

/-- Position on its 5-cycle (the centre has position 0). -/
def pos (i : Fin 9) : ℕ := if i.val ≤ 4 then i.val else i.val - 4
/-- 0 for the centre, 1 or 2 for the two wings. -/
def wing (i : Fin 9) : ℕ := if i.val = 0 then 0 else if i.val ≤ 4 then 1 else 2
def cyc (p q : ℕ) : ℕ := min (max p q - min p q) (5 - (max p q - min p q))
def toC (p : ℕ) : ℕ := min p (5 - p)

/-- Distance table: along one cycle, or through the centre between the wings. -/
def D (i j : Fin 9) : ℕ :=
  if wing i = 0 ∨ wing j = 0 ∨ wing i = wing j then cyc (pos i) (pos j)
  else toC (pos i) + toC (pos j)

theorem cert : BaseCert base D := ⟨by decide, by decide +kernel, by decide +kernel, by decide⟩

theorem dist_eq (u v : Fin 9) : base.dist u v = D u v :=
  (dist_eq_of_potential base D cert.zero cert.lip cert.desc u v).2

theorem connected : base.Connected :=
  ⟨fun u v => (dist_eq_of_potential base D cert.zero cert.lip cert.desc u v).1⟩

theorem diam_eq : base.diam = 4 := by
  have hne : base.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp connected
  apply le_antisymm
  · obtain ⟨u, v, h⟩ := base.exists_dist_eq_diam
    rw [← h, dist_eq]
    have : ∀ u v : Fin 9, D u v ≤ 4 := by decide
    exact this u v
  · have h := base.dist_le_diam hne (u := 2) (v := 6)
    rw [dist_eq] at h
    have h26 : D 2 6 = 4 := by decide
    omega

lemma reachable_const {V β : Type} {G' : SimpleGraph V} (f : V → β)
    (hf : ∀ u v, G'.Adj u v → f u = f v) {u v : V} (h : G'.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (hf _ _ ha).trans ih

/-- Deleting the centre `0` disconnects the base (it separates 2 from 6). -/
theorem hasCutVertex : HasCutVertex base := by
  refine ⟨0, fun h => ?_⟩
  have hw : ∀ u v : Fin 9, u ≠ 0 → v ≠ 0 → base.Adj u v → wing u = wing v := by decide
  have := reachable_const (G' := base.induce {v | v ≠ 0}) (fun x => wing x.1)
    (fun u v huv => hw u.1 v.1 u.2 v.2 huv)
    (h.preconnected ⟨2, show (2 : Fin 9) ≠ 0 by decide⟩ ⟨6, show (6 : Fin 9) ≠ 0 by decide⟩)
  exact absurd this (by decide)

/-- Weighted geodesic counts with fuel: walks along base geodesics, weighted by the
product of the part sizes `m` of the inner vertices. -/
def Fw (m : Fin 9 → ℕ) : ℕ → Fin 9 → Fin 9 → ℕ
  | 0, _, _ => 1
  | t + 1, i, j => if D i j ≤ 1 then 1 else
      ∑ k, if base.Adj i k ∧ D k j + 1 = D i j then m k * Fw m t k j else 0

def F (m : Fin 9 → ℕ) : Fin 9 → Fin 9 → ℕ := Fw m 4

/-- The fibre-level value of the betweenness formula for the wedge base. -/
def value (m P : Fin 9 → ℕ) (k : Fin 9) : ℚ :=
  (1 / 2) * ((∑ i, ∑ j, if i ≠ j ∧ i ≠ k ∧ j ≠ k then
      ((m i * m j : ℕ) : ℚ) * pairDep D (F m) i j k else 0) +
    ∑ i, if base.Adj i k then (P i : ℚ) / ((∑ l, if base.Adj i l then m l else 0 : ℕ) : ℚ)
      else 0)

theorem betweenness_eq_value {N : ℕ} {π : Fin N → Fin 9} {L : Type} [DecidableEq L]
    {κ : Fin N → L} (hπ : Function.Surjective π) (m P : Fin 9 → ℕ)
    (hm : ∀ i, fibreCard π i = m i) (hP : ∀ i, crossPairs π κ i = P i)
    (hchk : ∀ i j, i ≠ j → F m i j = if D i j = 1 then 1 else
      ∑ k, if base.Adj i k ∧ D k j + 1 = D i j then m k * F m k j else 0)
    (z : Fin N) :
    betweenness (blowUp base π (cluster κ)) z = value m P (π z) := by
  have hF : FCert base π D (F m) := by
    intro i j hij
    rw [hchk i j hij]
    simp only [hm]
  rw [betweenness_blowUp_cluster cert hπ hF z]
  unfold value nbrWeight
  simp only [hm, hP]

#print axioms cert
#print axioms diam_eq
#print axioms hasCutVertex
#print axioms betweenness_eq_value
end Wedge
end BlowupBetweenness
```

### `BlowupWitness.lean`

```lean
import BlowupWedgeBase

/-!
The 1061-vertex counterexample to Hartman–Pokorná Conjecture 12 and the endpoint.

Base: the wedge of two 5-cycles (`Wedge.base`). Parts: A₁ E₁ A₂ E₂ are K₁₀₀,
B₁ D₁ B₂ D₂ are K₅, and the centre is K₆₀₄ ⊔ K₈ ⊔ K₄ ⊔ 25·K₁ (641 vertices).
Every vertex has betweenness 100.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
namespace Witness1061
open Wedge

/-- Clique sizes of the 36 classes: classes 0..7 are the parts of base vertices 1..8,
classes 8..35 are the cliques of the centre. -/
def szList : List ℕ := [100, 5, 5, 100, 100, 5, 5, 100, 604, 8, 4] ++ List.replicate 25 1
def sz (c : Fin 36) : ℕ := szList.getD c.val 0
/-- The base vertex of each class. -/
def bf (c : Fin 36) : Fin 9 := if h : c.val < 8 then ⟨c.val + 1, by omega⟩ else 0
def pick (i : Fin 9) : Fin 36 := if i = 0 then 8 else ⟨i.val - 1, by omega⟩

/-- Number of vertices. -/
abbrev N : ℕ := ∑ c, sz c
theorem card_eq : N = 1061 := by decide +kernel

/-- The projection to the base. -/
def proj : Fin N → Fin 9 := partOf sz bf
/-- The graph `H` (restricted to each part it is `H_i`): a disjoint union of cliques. -/
def H : SimpleGraph (Fin N) := cluster (classOf sz)
instance : DecidableRel H.Adj := inferInstanceAs (DecidableRel (cluster (classOf sz)).Adj)

/-- The blow-up `G[H₁, …, H₉]`. -/
def X : SimpleGraph (Fin N) := blowUp base proj H
instance : DecidableRel X.Adj := inferInstanceAs (DecidableRel (blowUp base proj H).Adj)

theorem surj : Function.Surjective proj :=
  partOf_surjective sz bf pick (by decide)

def mTab (i : Fin 9) : ℕ := if i = 0 then 641 else if pos i = 1 ∨ pos i = 4 then 100 else 5
def PTab (i : Fin 9) : ℕ := if i = 0 then 45960 else 0

theorem fibre_sizes (i : Fin 9) : fibreCard proj i = mTab i := by
  unfold proj
  rw [fibreCard_partOf]
  revert i
  decide +kernel

theorem cross_pairs (i : Fin 9) : crossPairs proj (classOf sz) i = PTab i := by
  unfold proj
  rw [crossPairs_partOf]
  revert i
  decide +kernel

theorem walk_counts : ∀ i j : Fin 9, i ≠ j → F mTab i j = if D i j = 1 then 1 else
    ∑ k, if base.Adj i k ∧ D k j + 1 = D i j then mTab k * F mTab k j else 0 := by
  decide +kernel

theorem values : ∀ k : Fin 9, value mTab PTab k = 100 := by decide +kernel

/-- Every vertex of the blow-up has betweenness 100. -/
theorem betweenness_X (z : Fin N) : betweenness X z = 100 := by
  rw [show betweenness X z = betweenness (blowUp base proj (cluster (classOf sz))) z from rfl,
    betweenness_eq_value surj mTab PTab fibre_sizes cross_pairs walk_counts z, values]

theorem connected_X : X.Connected := by
  have : Nonempty (Fin N) := ⟨finSigmaFinEquiv ⟨0, ⟨0, by decide⟩⟩⟩
  exact connectedX cert surj

theorem uniform_X : BetweennessUniform X := fun x y => by rw [betweenness_X, betweenness_X]

end Witness1061

open Wedge Witness1061 in
/-- **MathDB 350694.** Hartman–Pokorná Conjecture 12 is false: there are a connected
graph `G` of diameter at least 3 with a cut vertex and graphs `H_i` (nonempty) such that
the blow-up `G[H_1, …, H_n]` is betweenness-uniform. -/
theorem hartman_pokorna_conj12_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → 3 ≤ G.diam → HasCutVertex G →
        ∀ (N : ℕ) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
          Function.Surjective π → ¬ BetweennessUniform (blowUp G π H) := by
  intro h
  exact h 9 base connected (by rw [diam_eq]; decide) hasCutVertex N proj H surj uniform_X

theorem not_conjecture12 : ¬ Conjecture12 := hartman_pokorna_conj12_false

#print axioms Witness1061.betweenness_X
#print axioms Witness1061.connected_X
#print axioms hartman_pokorna_conj12_false
#print axioms not_conjecture12
end BlowupBetweenness
```

### `BlowupWitness3176.lean`

```lean
import BlowupWitness

/-!
The proof's own witness X₁ (3176 vertices), checked with the same machinery
(supplementary; the endpoint uses the 1061-vertex witness).

Base: the wedge of two 5-cycles. Parts: A₁ E₁ A₂ E₂ are K₂₈₈, B₁ D₁ B₂ D₂ are K₂₄,
and the centre is K₁₈₈₂ ⊔ K₄₁ ⊔ K₃ ⊔ K₁ ⊔ K₁ (1928 vertices).
Every vertex has betweenness 288.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
namespace Witness3176
open Wedge

/-- Clique sizes of the 13 classes: classes 0..7 are the parts of base vertices 1..8,
classes 8..12 are the cliques of the centre. -/
def szList : List ℕ := [288, 24, 24, 288, 288, 24, 24, 288, 1882, 41, 3, 1, 1]
def sz (c : Fin 13) : ℕ := szList.getD c.val 0
/-- The base vertex of each class. -/
def bf (c : Fin 13) : Fin 9 := if h : c.val < 8 then ⟨c.val + 1, by omega⟩ else 0
def pick (i : Fin 9) : Fin 13 := if i = 0 then 8 else ⟨i.val - 1, by omega⟩

/-- Number of vertices. -/
abbrev N : ℕ := ∑ c, sz c
theorem card_eq : N = 3176 := by decide +kernel

/-- The projection to the base. -/
def proj : Fin N → Fin 9 := partOf sz bf
/-- The graph `H` (restricted to each part it is `H_i`): a disjoint union of cliques. -/
def H : SimpleGraph (Fin N) := cluster (classOf sz)
instance : DecidableRel H.Adj := inferInstanceAs (DecidableRel (cluster (classOf sz)).Adj)

/-- The blow-up `G[H₁, …, H₉]`. -/
def X : SimpleGraph (Fin N) := blowUp base proj H
instance : DecidableRel X.Adj := inferInstanceAs (DecidableRel (blowUp base proj H).Adj)

theorem surj : Function.Surjective proj :=
  partOf_surjective sz bf pick (by decide)

def mTab (i : Fin 9) : ℕ := if i = 0 then 1928 else if pos i = 1 ∨ pos i = 4 then 288 else 24
def PTab (i : Fin 9) : ℕ := if i = 0 then 173568 else 0

theorem fibre_sizes (i : Fin 9) : fibreCard proj i = mTab i := by
  unfold proj
  rw [fibreCard_partOf]
  revert i
  decide +kernel

theorem cross_pairs (i : Fin 9) : crossPairs proj (classOf sz) i = PTab i := by
  unfold proj
  rw [crossPairs_partOf]
  revert i
  decide +kernel

theorem walk_counts : ∀ i j : Fin 9, i ≠ j → F mTab i j = if D i j = 1 then 1 else
    ∑ k, if base.Adj i k ∧ D k j + 1 = D i j then mTab k * F mTab k j else 0 := by
  decide +kernel

theorem values : ∀ k : Fin 9, value mTab PTab k = 288 := by decide +kernel

/-- Every vertex of the blow-up has betweenness 288. -/
theorem betweenness_X (z : Fin N) : betweenness X z = 288 := by
  rw [show betweenness X z = betweenness (blowUp base proj (cluster (classOf sz))) z from rfl,
    betweenness_eq_value surj mTab PTab fibre_sizes cross_pairs walk_counts z, values]

theorem connected_X : X.Connected := by
  have : Nonempty (Fin N) := ⟨finSigmaFinEquiv ⟨0, ⟨0, by decide⟩⟩⟩
  exact connectedX cert surj

theorem uniform_X : BetweennessUniform X := fun x y => by rw [betweenness_X, betweenness_X]

end Witness3176

#print axioms Witness3176.betweenness_X
#print axioms Witness3176.uniform_X
end BlowupBetweenness
```

### `BlowupGuards.lean`

```lean
import BlowupWitness3176
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
Guards for the definitions (requested by the review):
* every vertex of `C₅` (Mathlib's `cycleGraph 5`) has betweenness 1;
* in `P₃` (Mathlib's `pathGraph 3`) the middle vertex has betweenness 1 and the ends 0,
  so `P₃` is not betweenness-uniform (the predicate is not trivial);
* the source's Observation 3: `P₃[K₁, I₂, K₁]` is a 4-cycle and is betweenness-uniform
  (value 1/2).
All values come from the same general theorem used for the witness.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators
namespace BlowupBetweenness
namespace Guards
open SimpleGraph

lemma betweenness_congr {n : ℕ} {X Y : SimpleGraph (Fin n)} [DecidableRel X.Adj]
    [DecidableRel Y.Adj] (h : X = Y) (x : Fin n) : betweenness X x = betweenness Y x := by
  subst h
  congr 1

/-- The general formula with explicit tables. -/
theorem bw_eq {n N : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {D : Fin n → Fin n → ℕ}
    (hc : BaseCert G D) {π : Fin N → Fin n} {L : Type} [DecidableEq L] {κ : Fin N → L}
    (hπ : Function.Surjective π) (F : Fin n → Fin n → ℕ) (m P : Fin n → ℕ)
    (hm : ∀ i, fibreCard π i = m i) (hP : ∀ i, crossPairs π κ i = P i)
    (hchk : ∀ i j, i ≠ j → F i j = if D i j = 1 then 1 else
      ∑ k, if G.Adj i k ∧ D k j + 1 = D i j then m k * F k j else 0) (z : Fin N) :
    betweenness (blowUp G π (cluster κ)) z = (1 / 2) *
      ((∑ i, ∑ j, if i ≠ j ∧ i ≠ π z ∧ j ≠ π z then
          ((m i * m j : ℕ) : ℚ) * pairDep D F i j (π z) else 0) +
        ∑ i, if G.Adj i (π z) then (P i : ℚ) / ((∑ l, if G.Adj i l then m l else 0 : ℕ) : ℚ)
          else 0) := by
  have hF : FCert G π D F := by
    intro i j hij
    rw [hchk i j hij]
    simp only [hm]
  rw [betweenness_blowUp_cluster hc hπ hF z]
  unfold nbrWeight
  simp only [hm, hP]

lemma blowUp_id_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    blowUp G id (cluster (id : Fin n → Fin n)) = G := by
  ext u v
  simp only [blowUp, cluster, id]
  constructor
  · rintro (⟨-, h, h'⟩ | h)
    · exact absurd h' h
    · exact h
  · exact Or.inr

instance : DecidableRel (cycleGraph 5).Adj :=
  fun u v => inferInstanceAs (Decidable (u - v = 1 ∨ v - u = 1))

instance : DecidableRel (pathGraph 3).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-! ### C₅ -/

def c5D (i j : Fin 5) : ℕ := Wedge.cyc i.val j.val

theorem c5_cert : BaseCert (cycleGraph 5) c5D :=
  ⟨by decide, by decide +kernel, by decide +kernel, by decide⟩

theorem c5_betweenness (x : Fin 5) : betweenness (cycleGraph 5) x = 1 := by
  rw [← betweenness_congr (blowUp_id_eq (cycleGraph 5)) x,
    bw_eq c5_cert Function.surjective_id (fun _ _ => 1) (fun _ => 1) (fun _ => 0)
      (by decide) (by decide) (by decide +kernel) x]
  revert x
  decide +kernel

/-! ### P₃ -/

def p3D (i j : Fin 3) : ℕ := max i.val j.val - min i.val j.val

theorem p3_cert : BaseCert (pathGraph 3) p3D :=
  ⟨by decide, by decide +kernel, by decide +kernel, by decide⟩

theorem p3_betweenness :
    betweenness (pathGraph 3) 0 = 0 ∧ betweenness (pathGraph 3) 1 = 1 ∧
      betweenness (pathGraph 3) 2 = 0 := by
  have h := fun x => (betweenness_congr (blowUp_id_eq (pathGraph 3)) x).symm.trans
    (bw_eq p3_cert Function.surjective_id (fun _ _ => 1) (fun _ => 1) (fun _ => 0)
      (by decide) (by decide) (by decide +kernel) x)
  rw [h 0, h 1, h 2]
  decide +kernel

theorem p3_not_uniform : ¬ BetweennessUniform (pathGraph 3) := by
  intro h
  have := h 0 1
  rw [p3_betweenness.1, p3_betweenness.2.1] at this
  norm_num at this

/-! ### P₃[K₁, I₂, K₁] -/

/-- Parts: vertex 0 ↦ 0, vertices 1, 2 ↦ 1 (the edgeless `I₂`), vertex 3 ↦ 2. -/
def obsπ : Fin 4 → Fin 3 := ![0, 1, 1, 2]

lemma obs_H_eq : (⊥ : SimpleGraph (Fin 4)) = cluster (id : Fin 4 → Fin 4) := by
  ext u v
  simp [cluster]

/-- The blow-up is the 4-cycle `0 - 1 - 3 - 2 - 0` (relabel by `σ = [0, 1, 3, 2]`). -/
theorem obs_is_C4 :
    ∀ u v : Fin 4, (blowUp (pathGraph 3) obsπ ⊥).Adj u v ↔
      (cycleGraph 4).Adj (![0, 1, 3, 2] u) (![0, 1, 3, 2] v) := by
  have : ∀ u v : Fin 4, ((obsπ u = obsπ v ∧ False) ∨
      (obsπ u).val + 1 = (obsπ v).val ∨ (obsπ v).val + 1 = (obsπ u).val) ↔
      ((![0, 1, 3, 2] u : Fin 4) - ![0, 1, 3, 2] v = 1 ∨
        (![0, 1, 3, 2] v : Fin 4) - ![0, 1, 3, 2] u = 1) := by decide
  intro u v
  simpa [blowUp, pathGraph_adj, cycleGraph_adj] using this u v

theorem obs_surj : Function.Surjective obsπ := by decide

theorem obs_betweenness (x : Fin 4) :
    betweenness (blowUp (pathGraph 3) obsπ ⊥) x = 1 / 2 := by
  rw [betweenness_congr (by rw [obs_H_eq] : blowUp (pathGraph 3) obsπ ⊥ =
      blowUp (pathGraph 3) obsπ (cluster (id : Fin 4 → Fin 4))) x,
    bw_eq p3_cert obs_surj (fun i j => if i.val + j.val = 2 ∧ i ≠ j then 2 else 1)
      ![1, 2, 1] ![0, 2, 0] (by decide) (by decide) (by decide +kernel) x]
  revert x
  decide +kernel

theorem obs_uniform : BetweennessUniform (blowUp (pathGraph 3) obsπ ⊥) :=
  fun x y => by rw [obs_betweenness, obs_betweenness]

#print axioms c5_betweenness
#print axioms p3_betweenness
#print axioms p3_not_uniform
#print axioms obs_is_C4
#print axioms obs_uniform
end Guards
end BlowupBetweenness
```

### `BlowupAudit.lean`

```lean
import BlowupGuards

/-!
Audit: the endpoint statement, the definitions it depends on, a summary of the
witness facts, and the axioms of every endpoint.
-/

open BlowupBetweenness

/-- The endpoint is literally the negation of the conjecture as stated. -/
example : Conjecture12 ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → 3 ≤ G.diam → HasCutVertex G →
    ∀ (N : ℕ) (π : Fin N → Fin n) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
      Function.Surjective π → ¬ BetweennessUniform (blowUp G π H) := Iff.rfl

/-- Summary of the witness: the base is connected, has diameter 4 and the cut vertex 0;
the blow-up has 1061 vertices, every part is nonempty, it is connected, and every
vertex has betweenness 100. -/
theorem witness_summary :
    Wedge.base.Connected ∧ Wedge.base.diam = 4 ∧
      ¬ (Wedge.base.induce {v | v ≠ 0}).Connected ∧
      Witness1061.N = 1061 ∧ Function.Surjective Witness1061.proj ∧
      Witness1061.X.Connected ∧ (∀ z, betweenness Witness1061.X z = 100) := by
  refine ⟨Wedge.connected, Wedge.diam_eq, ?_, Witness1061.card_eq, Witness1061.surj,
    Witness1061.connected_X, Witness1061.betweenness_X⟩
  intro h
  have hw : ∀ u v : Fin 9, u ≠ 0 → v ≠ 0 → Wedge.base.Adj u v → Wedge.wing u = Wedge.wing v := by
    decide
  have := Wedge.reachable_const (G' := Wedge.base.induce {v | v ≠ 0}) (fun x => Wedge.wing x.1)
    (fun u v huv => hw u.1 v.1 u.2 v.2 huv)
    (h.preconnected ⟨2, show (2 : Fin 9) ≠ 0 by decide⟩ ⟨6, show (6 : Fin 9) ≠ 0 by decide⟩)
  exact absurd this (by decide)

#check @hartman_pokorna_conj12_false
#check @not_conjecture12
#check @witness_summary
#check @Witness3176.betweenness_X
#check @Guards.c5_betweenness
#check @Guards.p3_betweenness
#check @Guards.p3_not_uniform
#check @Guards.obs_is_C4
#check @Guards.obs_uniform
#print Conjecture12
#print blowUp
#print HasCutVertex
#print BetweennessUniform
#print betweenness
#print sigma
#print sigmaThrough
#print cluster
#print axioms hartman_pokorna_conj12_false
#print axioms not_conjecture12
#print axioms witness_summary
#print axioms Witness3176.betweenness_X
#print axioms Guards.c5_betweenness
#print axioms Guards.p3_betweenness
#print axioms Guards.p3_not_uniform
#print axioms Guards.obs_is_C4
#print axioms Guards.obs_uniform
```


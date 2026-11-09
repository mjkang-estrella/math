/-
MathDB 352972: balanced-graph conjecture for flat graphs -- literal refutation.

Source: Hossein Teimoori Faal, "On Clique Roots of Flat Graphs", arXiv:2112.09721v1.
Definition 2.2 (p4): flat = every edge lies in at most two triangles (3-cliques).
Conjecture 2 (p6): every flat graph is balanced, i.e. the absolute difference
between the odd-clique count sum and the even-clique count sum is at most 1
(c_0 = 1 is counted among the even cliques).

Endpoint: refutation of the universal statement over ALL finite simple graphs,
by the finite simple graph K_{3,3}: flat, yet discrepancy 4 > 1 with c_0
(and 3 > 1 under the positive-index convention).

Pins: Lean v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52),
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# MathDB 352972: balanced-graph conjecture for flat graphs, literal refutation

Universal endpoint: `NOT (for all finite simple graphs G, flat G -> balanced G)`,
witnessed by `K_{3,3}` with clique-count discrepancy 4 > 1 (c_0 = 1 convention)
and 3 > 1 (positive-index convention).
-/

open BigOperators

namespace FlatBalance

/-! ## Simple graphs -/

/-- A simple undirected graph: irreflexive symmetric adjacency (no loops,
undirected).  Finiteness is carried by a `Fintype` instance on the vertex
type, never by the structure itself. -/
structure SimpleGraph (V : Type) where
  /-- The adjacency relation. -/
  Adj : V → V → Prop
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ a b, Adj a b → Adj b a
  /-- Adjacency is irreflexive. -/
  adj_irrefl : ∀ a, ¬ Adj a a

/-! ## Cliques, triangles, counts, flatness, balance

The data-level definitions below use classical decidability for the
clique/triangle predicates; this contributes at most the axiom
`Classical.choice`, which is on the allowed list. -/

open Classical

/-- `s` is a clique of `G`: all its vertices are pairwise adjacent. -/
def IsClique {V : Type} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b

/-- The set of `k`-cliques: `k`-element vertex subsets which are cliques.
This is `c_k(G)` as a Finset; every subset of the vertex type is eligible
since it is automatically a subset of `univ`. -/
noncomputable def cliqueFinset {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Finset (Finset V) :=
  ((Finset.univ : Finset V).powerset).filter fun s => s.card = k ∧ IsClique G s

/-- The number `c_k(G)` of `k`-cliques of `G`. -/
noncomputable def cliqueCount {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (cliqueFinset G k).card

/-- Membership characterization of the `k`-clique set. -/
theorem mem_cliqueFinset {V : Type} [Fintype V] {G : SimpleGraph V} {s : Finset V} {k : ℕ} :
    s ∈ cliqueFinset G k ↔ s.card = k ∧ IsClique G s := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and]

/-- A triangle of `G`: a three-element clique, exactly the source's notion of
a triangle (3-clique) on which edge-incidence is counted. -/
def IsTriangle {V : Type} (G : SimpleGraph V) (s : Finset V) : Prop :=
  s.card = 3 ∧ IsClique G s

/-- The Finset of triangles of `G` containing both `a` and `b`:
the edge-in-triangle incidence set of source Definition 2.2. -/
noncomputable def triangleSet {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V) :
    Finset (Finset V) :=
  ((Finset.univ : Finset V).powerset).filter fun s => IsTriangle G s ∧ a ∈ s ∧ b ∈ s

/-- The common neighbours of `a` and `b`. -/
noncomputable def commonNbrFinset {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V) :
    Finset V :=
  Finset.univ.filter fun c => G.Adj a c ∧ G.Adj b c

/-- Flatness, source Definition 2.2: every edge lies in at most two triangles.
No planarity, connectedness or no-isolated-edge condition is imposed. -/
noncomputable def Flat {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ a b, G.Adj a b → (triangleSet G a b).card ≤ 2

/-- The sum of the `c_k(G)` over odd `k`, up to the vertex count. -/
noncomputable def oddCliqueSum {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1), if d % 2 = 1 then cliqueCount G d else 0

/-- The sum of the `c_k(G)` over even `k` *including* `k = 0` (source
convention `c_0 = 1`), up to the vertex count. -/
noncomputable def evenCliqueSum {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1), if d % 2 = 0 then cliqueCount G d else 0

/-- The sum over even `k ≥ 1` only (positive-index convention, no `c_0`). -/
noncomputable def evenCliqueSumPos {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ∑ d ∈ Finset.range (Fintype.card V + 1),
    if d % 2 = 0 ∧ 0 < d then cliqueCount G d else 0

/-- The clique-count discrepancy `D_clique(G)` of the source, equation (14):
the absolute value of the difference of the odd and even sums, as a
natural number via `Int.natAbs` (the exact absolute value on Z). -/
noncomputable def discrepancyNat {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSum G : ℤ))

/-- The discrepancy under the positive-index convention (no `c_0`). -/
noncomputable def discrepancyNatPos {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Int.natAbs ((oddCliqueSum G : ℤ) - (evenCliqueSumPos G : ℤ))

/-- Balanced: `D_clique(G) ≤ 1`. -/
noncomputable def Balanced {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  discrepancyNat G ≤ 1

/-! ## The witness K_{3,3} -/

/-- Adjacency of the witness: vertices are adjacent iff they lie in different
summands of `Fin 3 ⊕ Fin 3`. -/
def K33Adj : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

/-- The witness graph `K_{3,3}`: two disjoint three-element sides, all and
only cross edges.  A genuine finite simple graph: irreflexive and symmetric. -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj := K33Adj
  adj_symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact trivial
    · exact trivial
    · exact h
  adj_irrefl := by
    intro a
    cases a <;> simp [K33Adj]

/-- Unfolding lemma for the witness adjacency, left-to-right. -/
theorem K33_adj_il_ir (i j : Fin 3) : K33.Adj (Sum.inl i) (Sum.inr j) := trivial

/-- Unfolding lemma for the witness adjacency, right-to-left. -/
theorem K33_adj_ir_il (i j : Fin 3) : K33.Adj (Sum.inr i) (Sum.inl j) := trivial

/-- No adjacency within the left side. -/
theorem K33_not_adj_ll (i j : Fin 3) : ¬ K33.Adj (Sum.inl i) (Sum.inl j) := id

/-- No adjacency within the right side. -/
theorem K33_not_adj_rr (i j : Fin 3) : ¬ K33.Adj (Sum.inr i) (Sum.inr j) := id

/-- An edge of the witness has its endpoints on opposite sides. -/
theorem K33_adj_opposite {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) :
    (∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∨ (∃ i j, a = Sum.inr i ∧ b = Sum.inl j) := by
  cases a <;> cases b
  case inl.inl => exact absurd h (K33_not_adj_ll _ _)
  case inl.inr => exact Or.inl ⟨_, _, rfl, rfl⟩
  case inr.inl => exact Or.inr ⟨_, _, rfl, rfl⟩
  case inr.inr => exact absurd h (K33_not_adj_rr _ _)

/-- Adjacent vertices of the witness are distinct (faithfulness of the
simple-graph structure: no edge is a loop). -/
theorem K33_adj_ne {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) : a ≠ b := by
  intro e
  subst e
  exact K33.adj_irrefl _ h

/-- Symmetry of the witness adjacency, as a usable lemma. -/
theorem K33_symm {a b : Fin 3 ⊕ Fin 3} (h : K33.Adj a b) : K33.Adj b a :=
  K33.adj_symm a b h



/-! ## Witness cardinality and clique counting -/

/-- The witness vertex type has exactly six elements. -/
theorem card_V6 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
  rw [Fintype.card_sum, Fintype.card_fin]

/-- Left-side and right-side vertices are distinct. -/
theorem inl_ne_inr (i j : Fin 3) : (Sum.inl i : Fin 3 ⊕ Fin 3) ≠ Sum.inr j := by
  intro e
  cases e

/-- Two-element sets commute. -/
theorem insert_pair_comm (x y : Fin 3 ⊕ Fin 3) :
    insert x ({y} : Finset (Fin 3 ⊕ Fin 3)) = insert y ({x} : Finset (Fin 3 ⊕ Fin 3)) := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    rcases hz with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro hz
    rcases hz with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The cross pair `{left i, right j}` as a set. -/
def pairFinset (p : Fin 3 × Fin 3) : Finset (Fin 3 ⊕ Fin 3) :=
  insert (Sum.inl p.1) ({Sum.inr p.2} : Finset (Fin 3 ⊕ Fin 3))

/-- Any clique of the witness has at most two vertices: among any three
vertices, two lie on the same side and are then nonadjacent. -/
theorem K33_clique_card_le (s : Finset (Fin 3 ⊕ Fin 3)) (h : IsClique K33 s) :
    s.card ≤ 2 := by
  by_contra hc
  have h3 : 3 ≤ s.card := by omega
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  have hne2 : (s.erase a).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ := hne2
  have hab : b ≠ a ∧ b ∈ s := Finset.mem_erase.mp hb
  have hb' : b ∈ s := hab.2
  have hba : b ≠ a := hab.1
  have hbE : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hba, hb'⟩
  have h2 : ((s.erase a).erase b).card = (s.erase a).card - 1 :=
    Finset.card_erase_of_mem hbE
  have hne3 : ((s.erase a).erase b).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hne3
  have hcb : c ≠ b ∧ c ∈ s.erase a := Finset.mem_erase.mp hc
  have hca : c ≠ a ∧ c ∈ s := Finset.mem_erase.mp hcb.2
  have hcc : c ∈ s := hca.2
  have hne_ab : a ≠ b := Ne.symm hba
  have hne_ac : a ≠ c := Ne.symm hca.1
  have hne_bc : b ≠ c := Ne.symm hcb.1
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
  · exact absurd (h (Sum.inl a) ha (Sum.inl b) hb' hne_ab) (K33_not_adj_ll _ _)
  · exact absurd (h (Sum.inl a) ha (Sum.inl b) hb' hne_ab) (K33_not_adj_ll _ _)
  · exact absurd (h (Sum.inl a) ha (Sum.inl c) hcc hne_ac) (K33_not_adj_ll _ _)
  · exact absurd (h (Sum.inr b) hb' (Sum.inr c) hcc hne_bc) (K33_not_adj_rr _ _)
  · exact absurd (h (Sum.inr b) hb' (Sum.inr c) hcc hne_bc) (K33_not_adj_ll _ _)
  · exact absurd (h (Sum.inr a) ha (Sum.inr c) hcc hne_ac) (K33_not_adj_rr _ _)
  · exact absurd (h (Sum.inr a) ha (Sum.inr b) hb' hne_ab) (K33_not_adj_rr _ _)
  · exact absurd (h (Sum.inr a) ha (Sum.inr b) hb' hne_ab) (K33_not_adj_rr _ _)

/-- Membership in the triangle-incidence set. -/
theorem mem_triangleSet {V : Type} [Fintype V] {G : SimpleGraph V} {a b : V}
    {s : Finset V} :
    s ∈ triangleSet G a b ↔ (s.card = 3 ∧ IsClique G s) ∧ a ∈ s ∧ b ∈ s := by
  simp only [triangleSet, IsTriangle, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]

/-- The witness has no triangles at all: every triangle-incidence set is
empty. -/
theorem K33_triangleSet_empty (a b : Fin 3 ⊕ Fin 3) :
    triangleSet K33 a b = ∅ := by
  ext s
  rw [mem_triangleSet]
  constructor
  · rintro ⟨⟨h3, hcl⟩, -, -⟩
    have hle := K33_clique_card_le s hcl
    have hF : False := by omega
    exact hF.elim
  · intro hmem
    exact absurd hmem (Finset.notMem_empty s)

/-- Flatness of the witness: every edge lies in zero, hence at most two,
triangles. -/
theorem K33_flat : Flat K33 := by
  intro a b _
  rw [K33_triangleSet_empty, Finset.card_empty]
  exact Nat.zero_le 2

/-- c_0 = 1: the empty set is the unique 0-clique. -/
theorem cliqueCount_K33_zero : cliqueCount K33 0 = 1 := by
  have h : cliqueFinset K33 0 = {∅} := by
    ext s
    rw [mem_cliqueFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, -⟩
      exact Finset.card_eq_zero.mp hc
    · rintro rfl
      refine ⟨Finset.card_empty, ?_⟩
      intro a ha b hb _
      exact absurd ha (Finset.notMem_empty a)
  show (cliqueFinset K33 0).card = 1
  rw [h, Finset.card_singleton]

/-- Singletons are cliques of the witness. -/
theorem K33_clique_singleton (v : Fin 3 ⊕ Fin 3) : IsClique K33 ({v} : Finset (Fin 3 ⊕ Fin 3)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact absurd rfl hxy

/-- c_1 = 6: the 1-cliques are exactly the singletons of the six vertices. -/
theorem cliqueCount_K33_one : cliqueCount K33 1 = 6 := by
  have hset : cliqueFinset K33 1 =
      (Finset.univ : Finset (Fin 3 ⊕ Fin 3)).image
        (fun v : Fin 3 ⊕ Fin 3 => ({v} : Finset (Fin 3 ⊕ Fin 3))) := by
    ext s
    rw [mem_cliqueFinset, Finset.mem_image]
    constructor
    · rintro ⟨hc, -⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
      exact ⟨a, Finset.mem_univ _, ha.symm⟩
    · rintro ⟨a, -, hs⟩
      have hs' : ({a} : Finset (Fin 3 ⊕ Fin 3)) = s := hs
      have h1 : ({a} : Finset (Fin 3 ⊕ Fin 3)).card = 1 := Finset.card_singleton
      have h2 : IsClique ({a} : Finset (Fin 3 ⊕ Fin 3)) := K33_clique_singleton a
      rw [← hs']
      exact ⟨h1, h2⟩
  show (cliqueFinset K33 1).card = 6
  rw [hset, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_univ, card_V6]

/-- The pair `{left i, right j}` is a clique of the witness. -/
theorem K33_clique_pair (i j : Fin 3) :
    IsClique K33 (insert (Sum.inl i) ({Sum.inr j} : Finset (Fin 3 ⊕ Fin 3))) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact K33_adj_il_ir _ _
  · exact K33_adj_ir_il _ _
  · exact absurd rfl hxy

/-- The 2-cliques of the witness are exactly the cross pairs. -/
theorem cliqueFinset_K33_two : cliqueFinset K33 2 =
    (Finset.univ : Finset (Fin 3 × Fin 3)).image pairFinset := by
  ext s
  rw [mem_cliqueFinset, Finset.mem_image]
  constructor
  · rintro ⟨hc, hcl⟩
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hc
    have hxm : x ∈ s := by rw [hs]; simp
    have hym : y ∈ s := by rw [hs]; simp
    have hxya : K33.Adj x y := hcl x hxm y hym hxy
    rcases K33_adj_opposite hxya with ⟨i, j, hxi, hyj⟩ | ⟨i, j, hxi, hyj⟩
    · refine ⟨(i, j), Finset.mem_univ _, ?_⟩
      show insert (Sum.inl i) ({Sum.inr j} : Finset (Fin 3 ⊕ Fin 3)) = s
      rw [hs, hxi, hyj]
    · refine ⟨(j, i), Finset.mem_univ _, ?_⟩
      show insert (Sum.inl j) ({Sum.inr i} : Finset (Fin 3 ⊕ Fin 3)) = s
      rw [hs, hxi, hyj]
      exact insert_pair_comm _ _
  · rintro ⟨p, -, hp⟩
    rw [← hp]
    refine ⟨?_, ?_⟩
    · show (insert (Sum.inl p.1) ({Sum.inr p.2} : Finset (Fin 3 ⊕ Fin 3))).card = 2
      rw [Finset.card_insert_of_notMem (by
        intro hm
        simp only [Finset.mem_singleton] at hm
        exact absurd hm (inl_ne_inr _ _)), Finset.card_singleton]
    · exact K33_clique_pair _ _

/-- c_2 = 9: the 2-cliques are exactly the nine cross pairs, via the explicit
injection `(i, j) ↦ {left i, right j}`. -/
theorem cliqueCount_K33_two : cliqueCount K33 2 = 9 := by
  show (cliqueFinset K33 2).card = 9
  have hinj : Function.Injective pairFinset := by
    intro p q hEq
    have h1 : Sum.inl p.1 ∈ pairFinset q := by
      rw [← hEq]
      show Sum.inl p.1 ∈ insert (Sum.inl p.1) ({Sum.inr p.2} : Finset (Fin 3 ⊕ Fin 3))
      exact Finset.mem_insert_self _ _
    have h2 : Sum.inr p.2 ∈ pairFinset q := by
      rw [← hEq]
      show Sum.inr p.2 ∈ insert (Sum.inl p.1) ({Sum.inr p.2} : Finset (Fin 3 ⊕ Fin 3))
      exact Finset.mem_insert_of_mem (by simp)
    have h1' : Sum.inl p.1 ∈ insert (Sum.inl q.1) ({Sum.inr q.2} : Finset (Fin 3 ⊕ Fin 3)) := h1
    have h2' : Sum.inr p.2 ∈ insert (Sum.inl q.1) ({Sum.inr q.2} : Finset (Fin 3 ⊕ Fin 3)) := h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1' h2'
    rcases h1' with e | e
    · have hii : p.1 = q.1 := Sum.inl.inj e
      rcases h2' with e2 | e2
      · exact absurd e2.symm (inl_ne_inr _ _)
      · exact Prod.ext hii (Sum.inr.inj e2)
    · exact absurd e (inl_ne_inr _ _)
  rw [cliqueFinset_K33_two, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    card_V6]

/-- No 3-cliques: any clique has at most two vertices. -/
theorem cliqueFinset_K33_ge3 (k : ℕ) (hk : 3 ≤ k) : cliqueFinset K33 k = ∅ := by
  ext s
  rw [mem_cliqueFinset]
  constructor
  · rintro ⟨hc, hcl⟩
    have hle := K33_clique_card_le s hcl
    have hF : False := by omega
    exact hF.elim
  · intro hmem
    exact absurd hmem (Finset.notMem_empty s)

/-- No clique counts above 2 for the witness. -/
theorem cliqueCount_K33_ge3 (k : ℕ) (hk : 3 ≤ k) : cliqueCount K33 k = 0 := by
  show (cliqueFinset K33 k).card = 0
  rw [cliqueFinset_K33_ge3 k hk, Finset.card_empty]

theorem cliqueCount_K33_three : cliqueCount K33 3 = 0 := cliqueCount_K33_ge3 3 (by omega)

theorem cliqueCount_K33_four : cliqueCount K33 4 = 0 := cliqueCount_K33_ge3 4 (by omega)

theorem cliqueCount_K33_five : cliqueCount K33 5 = 0 := cliqueCount_K33_ge3 5 (by omega)

theorem cliqueCount_K33_six : cliqueCount K33 6 = 0 := cliqueCount_K33_ge3 6 (by omega)
end FlatBalance

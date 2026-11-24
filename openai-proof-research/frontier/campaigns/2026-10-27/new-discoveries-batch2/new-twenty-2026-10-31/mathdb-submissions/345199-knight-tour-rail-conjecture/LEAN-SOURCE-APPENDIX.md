# Lean source appendix (MathDB 345199)

Modules in import order, byte-identical to `src/`. Endpoint: `Rail.rail_conjecture_false` in `RailMain.lean`.

### `RailStatement.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Basic.Real.Basic

/-!
# Parberry's Rail Conjecture: definitions and statement

Source: I. Parberry, *Tourneys and the Fast Generation and Obfuscation of Closed Knight's
Tours*, arXiv:2001.06044v1.

* §2: the `n × n` knight's graph `K_n` has one vertex per cell and an edge between `u` and `v`
  iff a knight can move from `u` to `v`; the displacements are
  `M = {(±x, ±y) | x, y ∈ {1, 2} and x + y = 3}`.
  "A knight's tour is a Hamiltonian cycle on a knight's graph."
* §4: "A rail in a subgraph G = (V, E) of a knight's graph K consists of a pair of parallel
  moves between cells that are separated by knights moves that are not present in G, that is,
  an unordered pair of edges r = (e, e') such that e = (v0, v1) ∈ G, e' = (v2, v3) ∈ G, and
  (v0, v2), (v1, v3) ∈ K \ G."
* §4: "Conjecture. (The Rail Conjecture) An n × n knight's tour has Ω(n) rails."
-/

namespace Rail

/-- Knight adjacency of two cells of the `n × n` board. -/
def KnightAdj (n : ℕ) (a b : Fin n × Fin n) : Prop :=
  ((((a.1 : ℤ) - b.1).natAbs = 1 ∧ ((a.2 : ℤ) - b.2).natAbs = 2) ∨
   (((a.1 : ℤ) - b.1).natAbs = 2 ∧ ((a.2 : ℤ) - b.2).natAbs = 1))

/-- The `n × n` knight's graph `K_n`. -/
def knightGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj := KnightAdj n
  symm := by
    refine ⟨fun a b h => ?_⟩
    unfold KnightAdj at *
    have h1 : ((b.1 : ℤ) - a.1).natAbs = ((a.1 : ℤ) - b.1).natAbs := by
      rw [show (b.1 : ℤ) - a.1 = -((a.1 : ℤ) - b.1) by omega, Int.natAbs_neg]
    have h2 : ((b.2 : ℤ) - a.2).natAbs = ((a.2 : ℤ) - b.2).natAbs := by
      rw [show (b.2 : ℤ) - a.2 = -((a.2 : ℤ) - b.2) by omega, Int.natAbs_neg]
    rw [h1, h2]; exact h
  loopless := by
    refine ⟨fun a h => ?_⟩
    unfold KnightAdj at h
    simp at h

instance (n : ℕ) : DecidableRel (knightGraph n).Adj := by
  intro a b; unfold knightGraph KnightAdj; infer_instance

/-- A rail of the subgraph with edge set `G` (source §4, literally): an unordered pair `{e, e'}`
of edges with `e = (v0, v1) ∈ G`, `e' = (v2, v3) ∈ G`, and `(v0, v2)`, `(v1, v3)` knight moves
that are not in `G`. -/
def IsRail {n : ℕ} (G : Finset (Sym2 (Fin n × Fin n))) (r : Sym2 (Sym2 (Fin n × Fin n))) :
    Prop :=
  ∃ v0 v1 v2 v3 : Fin n × Fin n,
    r = s(s(v0, v1), s(v2, v3)) ∧ s(v0, v1) ∈ G ∧ s(v2, v3) ∈ G ∧
    (knightGraph n).Adj v0 v2 ∧ s(v0, v2) ∉ G ∧ (knightGraph n).Adj v1 v3 ∧ s(v1, v3) ∉ G

open Classical in
/-- The set of rails of a closed knight's tour `p` (its subgraph is the edge set of `p`). -/
noncomputable def rails {n : ℕ} {v : Fin n × Fin n} (p : (knightGraph n).Walk v v) :
    Finset (Sym2 (Sym2 (Fin n × Fin n))) :=
  Finset.univ.filter (IsRail p.edges.toFinset)

/-- The Rail Conjecture: there are `c > 0` and `N` such that every closed knight's tour of an
`n × n` board with `n ≥ N` has at least `c n` rails. -/
def RailConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (v : Fin n × Fin n) (p : (knightGraph n).Walk v v),
    p.IsHamiltonianCycle → c * (n : ℝ) ≤ ((rails p).card : ℝ)

end Rail
```

### `RailFamily.lean`

```lean
import Mathlib.Logic.Relation
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# The periodic family of boards and the local-view lemma

A reference table `T : ℤ → ℤ → ℕ → Bool` describes a 2-factor of the `N0 × N0` knight graph
(`N0 = 60`): `T x y d` says that the cell `(x, y)` uses knight move `d`. The board of side
`m = N0 + 8 t` repeats the middle period (8 columns, 8 rows) `t` more times; formally each
coordinate is sent to the reference by `tau m`, and the edge `{u, u + move d}` is present iff
the reference has it at `tau u` (or, read from the other end, at `tau (u + move d)`).

The *view lemma* says that around any cell, the board looks like the reference around a
suitable reference cell, provided the reference table is 8-periodic on the strip `[6, 54)` in
each coordinate. Everything below is generic in `T`.
-/

namespace Rail

/-- The knight moves, numbered `0 … 7`:
`(1,2),(2,1),(2,-1),(1,-2),(-1,-2),(-2,-1),(-2,1),(-1,2)`. Move `d + 4` is the negation of `d`. -/
def mvx : ℕ → ℤ
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 1 | 4 => -1 | 5 => -2 | 6 => -2 | _ => -1

def mvy : ℕ → ℤ
  | 0 => 2 | 1 => 1 | 2 => -1 | 3 => -2 | 4 => -2 | 5 => -1 | 6 => 1 | _ => 2

def negd (d : ℕ) : ℕ := (d + 4) % 8

lemma mv_negd {d : ℕ} (hd : d < 8) :
    mvx (negd d) = - mvx d ∧ mvy (negd d) = - mvy d ∧ negd d < 8 ∧ negd (negd d) = d := by
  unfold negd
  interval_cases d <;> simp [mvx, mvy]

lemma mv_bound {d : ℕ} :
    -2 ≤ mvx d ∧ mvx d ≤ 2 ∧ -2 ≤ mvy d ∧ mvy d ≤ 2 := by
  unfold mvx mvy
  split <;> omega

/-- Size of the reference board. -/
notation "N0" => (60 : ℤ)

/-- Coordinate map from a board of side `m` to the reference board. -/
def tau (m x : ℤ) : ℤ :=
  if x < 14 then x else if m - 14 ≤ x then x - (m - N0) else 14 + (x - 14) % 8

/-- Board sides of the family. -/
def Fam (m : ℤ) : Prop := ∃ t : ℕ, m = N0 + 8 * t

def OnB (m n : ℤ) (u : ℤ × ℤ) : Prop := 0 ≤ u.1 ∧ u.1 < m ∧ 0 ≤ u.2 ∧ u.2 < n

instance (m n : ℤ) (u : ℤ × ℤ) : Decidable (OnB m n u) := by unfold OnB; infer_instance

/-- Two coordinates are equivalent if equal, or both in the periodic strip and congruent
mod 8. -/
def Eqv (a b : ℤ) : Prop := a = b ∨ (6 ≤ a ∧ a < 54 ∧ 6 ≤ b ∧ b < 54 ∧ (a - b) % 8 = 0)

section
variable (T : ℤ → ℤ → ℕ → Bool)

/-- Adjacency in the board `m × n` of the family. -/
def AdjB (m n : ℤ) (u v : ℤ × ℤ) : Prop :=
  OnB m n u ∧ OnB m n v ∧ ∃ d, d < 8 ∧ v = (u.1 + mvx d, u.2 + mvy d) ∧
    (T (tau m u.1) (tau n u.2) d = true ∨ T (tau m v.1) (tau n v.2) (negd d) = true)

/-- Adjacency in the reference board. -/
def Adj0 (u v : ℤ × ℤ) : Prop :=
  OnB N0 N0 u ∧ OnB N0 N0 v ∧ ∃ d, d < 8 ∧ v = (u.1 + mvx d, u.2 + mvy d) ∧
    (T u.1 u.2 d = true ∨ T v.1 v.2 (negd d) = true)

/-- 8-periodicity of the reference table on the strip, in `x` (for every `y`). -/
def PerX : Prop := ∀ x y : ℤ, ∀ d : ℕ, 6 ≤ x → x + 8 < 54 → T x y d = T (x + 8) y d

/-- 8-periodicity of the reference table on the strip, in `y` (for every `x`). -/
def PerY : Prop := ∀ x y : ℤ, ∀ d : ℕ, 6 ≤ y → y + 8 < 54 → T x y d = T x (y + 8) d

variable {T}

lemma adjB_symm {m n : ℤ} {u v : ℤ × ℤ} (h : AdjB T m n u v) : AdjB T m n v u := by
  obtain ⟨hu, hv, d, hd, rfl, h⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := mv_negd hd
  refine ⟨hv, hu, negd d, h3, ?_, ?_⟩
  · ext <;> simp [h1, h2]
  · rw [h4]
    simp only at h ⊢
    exact h.symm

lemma adj0_symm {u v : ℤ × ℤ} (h : Adj0 T u v) : Adj0 T v u := by
  obtain ⟨hu, hv, d, hd, rfl, h⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := mv_negd hd
  refine ⟨hv, hu, negd d, h3, ?_, ?_⟩
  · ext <;> simp [h1, h2]
  · rw [h4]
    simp only at h ⊢
    exact h.symm

lemma T_shift_x (hP : PerX T) (y : ℤ) (d : ℕ) :
    ∀ k : ℕ, ∀ a : ℤ, 6 ≤ a → a + 8 * k < 54 → T a y d = T (a + 8 * k) y d := by
  intro k
  induction k with
  | zero => intro a _ _; simp
  | succ k ih =>
    intro a h1 h2
    rw [ih a h1 (by omega), hP _ _ _ (by omega) (by push_cast at h2; omega)]
    congr 1; push_cast; ring

lemma T_shift_y (hQ : PerY T) (x : ℤ) (d : ℕ) :
    ∀ k : ℕ, ∀ a : ℤ, 6 ≤ a → a + 8 * k < 54 → T x a d = T x (a + 8 * k) d := by
  intro k
  induction k with
  | zero => intro a _ _; simp
  | succ k ih =>
    intro a h1 h2
    rw [ih a h1 (by omega), hQ _ _ _ (by omega) (by push_cast at h2; omega)]
    congr 1; push_cast; ring

lemma T_eqv_x (hP : PerX T) {a b : ℤ} (h : Eqv a b) (y : ℤ) (d : ℕ) : T a y d = T b y d := by
  rcases h with rfl | ⟨h1, h2, h3, h4, h5⟩
  · rfl
  rcases le_total a b with hab | hab
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + 8 * (k : ℤ) := ⟨((b - a) / 8).toNat, by omega⟩
    rw [hk]; exact T_shift_x hP y d k a h1 (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, a = b + 8 * (k : ℤ) := ⟨((a - b) / 8).toNat, by omega⟩
    rw [hk]; exact (T_shift_x hP y d k b h3 (by omega)).symm

lemma T_eqv_y (hQ : PerY T) {a b : ℤ} (h : Eqv a b) (x : ℤ) (d : ℕ) : T x a d = T x b d := by
  rcases h with rfl | ⟨h1, h2, h3, h4, h5⟩
  · rfl
  rcases le_total a b with hab | hab
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + 8 * (k : ℤ) := ⟨((b - a) / 8).toNat, by omega⟩
    rw [hk]; exact T_shift_y hQ x d k a h1 (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, a = b + 8 * (k : ℤ) := ⟨((a - b) / 8).toNat, by omega⟩
    rw [hk]; exact (T_shift_y hQ x d k b h3 (by omega)).symm

end

/-- `cx` is a view of the coordinate `x` of a side-`m` board for the offsets `lo … hi`:
the offset cells are on the board at the same time, and land on equivalent reference
coordinates. -/
def AxView (m x cx lo hi : ℤ) : Prop :=
  ∀ δ : ℤ, lo ≤ δ → δ ≤ hi →
    ((0 ≤ x + δ ∧ x + δ < m) ↔ (0 ≤ cx + δ ∧ cx + δ < N0)) ∧
    (0 ≤ x + δ → x + δ < m → Eqv (tau m (x + δ)) (cx + δ))

/-- The anchored view: every coordinate is viewed at `tau m x`, for offsets up to 8. -/
lemma view_anchor {m x : ℤ} (hm : Fam m) (h0 : 0 ≤ x) (h1 : x < m) :
    AxView m x (tau m x) (-8) 8 := by
  obtain ⟨t, rfl⟩ := hm
  intro δ hd1 hd2
  unfold tau Eqv
  constructor
  · constructor
    · intro h; split_ifs <;> omega
    · intro h; split_ifs at h <;> omega
  · intro h2 h3
    split_ifs <;> omega

/-- The left-aligned view: near the left (or top) edge every board of the family coincides
with the reference, up to periodicity, as long as offsets stay left of `54`. -/
lemma view_left {m x lo hi : ℤ} (hm : Fam m) (hr : x + hi < 54) :
    AxView m x x lo hi := by
  obtain ⟨t, rfl⟩ := hm
  intro δ hd1 hd2
  unfold tau Eqv
  constructor
  · omega
  · intro h2 h3
    split_ifs <;> omega

/-- On the reference board itself every coordinate views itself. -/
lemma view_ref {x lo hi : ℤ} : AxView N0 x x lo hi := by
  intro δ hd1 hd2
  unfold tau Eqv
  constructor
  · omega
  · intro h2 h3
    split_ifs <;> omega

/-- Cells of the reference within the offset box `[lx, hx] × [ly, hy]` around `c`. -/
def Box (c : ℤ × ℤ) (lx hx ly hy : ℤ) (p : ℤ × ℤ) : Prop :=
  lx ≤ p.1 - c.1 ∧ p.1 - c.1 ≤ hx ∧ ly ≤ p.2 - c.2 ∧ p.2 - c.2 ≤ hy

section
variable {T : ℤ → ℤ → ℕ → Bool}

lemma T_view (hP : PerX T) (hQ : PerY T) {m n : ℤ} {u c : ℤ × ℤ} {lx hx ly hy : ℤ}
    (vx : AxView m u.1 c.1 lx hx) (vy : AxView n u.2 c.2 ly hy) {a b : ℤ}
    (ha1 : lx ≤ a) (ha2 : a ≤ hx) (hb1 : ly ≤ b) (hb2 : b ≤ hy)
    (hon : OnB m n (u.1 + a, u.2 + b)) (d : ℕ) :
    T (tau m (u.1 + a)) (tau n (u.2 + b)) d = T (c.1 + a) (c.2 + b) d := by
  obtain ⟨h1, h2, h3, h4⟩ := hon
  rw [T_eqv_x hP ((vx a ha1 ha2).2 h1 h2), T_eqv_y hQ ((vy b hb1 hb2).2 h3 h4)]

lemma onB_view {m n : ℤ} {u c : ℤ × ℤ} {lx hx ly hy : ℤ}
    (vx : AxView m u.1 c.1 lx hx) (vy : AxView n u.2 c.2 ly hy) {a b : ℤ}
    (ha1 : lx ≤ a) (ha2 : a ≤ hx) (hb1 : ly ≤ b) (hb2 : b ≤ hy) :
    OnB m n (u.1 + a, u.2 + b) ↔ OnB N0 N0 (c.1 + a, c.2 + b) := by
  have := (vx a ha1 ha2).1
  have := (vy b hb1 hb2).1
  unfold OnB; simp only
  constructor
  · intro ⟨h1, h2, h3, h4⟩; tauto
  · intro ⟨h1, h2, h3, h4⟩; tauto

/-- The view lemma: adjacency between two cells within the view box of `u` is adjacency
between the corresponding cells of the reference board. -/
lemma adj_view (hP : PerX T) (hQ : PerY T) {m n : ℤ} {u c : ℤ × ℤ} {lx hx ly hy : ℤ}
    (vx : AxView m u.1 c.1 lx hx) (vy : AxView n u.2 c.2 ly hy) {a1 b1 a2 b2 : ℤ}
    (h1 : lx ≤ a1 ∧ a1 ≤ hx ∧ ly ≤ b1 ∧ b1 ≤ hy) (h2 : lx ≤ a2 ∧ a2 ≤ hx ∧ ly ≤ b2 ∧ b2 ≤ hy) :
    AdjB T m n (u.1 + a1, u.2 + b1) (u.1 + a2, u.2 + b2) ↔
      Adj0 T (c.1 + a1, c.2 + b1) (c.1 + a2, c.2 + b2) := by
  obtain ⟨p1, p2, p3, p4⟩ := h1
  obtain ⟨q1, q2, q3, q4⟩ := h2
  have o1 := onB_view vx vy p1 p2 p3 p4
  have o2 := onB_view vx vy q1 q2 q3 q4
  unfold AdjB Adj0
  simp only
  constructor
  · rintro ⟨hu, hv, d, hd, he, ht⟩
    simp only [Prod.mk.injEq] at he
    refine ⟨o1.1 hu, o2.1 hv, d, hd, ?_, ?_⟩
    · ext <;> simp <;> omega
    · rwa [T_view hP hQ vx vy p1 p2 p3 p4 hu, T_view hP hQ vx vy q1 q2 q3 q4 hv] at ht
  · rintro ⟨hu, hv, d, hd, he, ht⟩
    simp only [Prod.mk.injEq] at he
    have hu' := o1.2 hu
    have hv' := o2.2 hv
    refine ⟨hu', hv', d, hd, ?_, ?_⟩
    · ext <;> simp <;> omega
    · rwa [T_view hP hQ vx vy p1 p2 p3 p4 hu', T_view hP hQ vx vy q1 q2 q3 q4 hv']

/-- Path transfer: a reference walk inside the view box gives a walk on the board. -/
lemma path_view (hP : PerX T) (hQ : PerY T) {m n : ℤ} {u c : ℤ × ℤ} {lx hx ly hy : ℤ}
    (vx : AxView m u.1 c.1 lx hx) (vy : AxView n u.2 c.2 ly hy) {g : ℤ × ℤ}
    (h : Relation.ReflTransGen
      (fun a b => Adj0 T a b ∧ Box c lx hx ly hy a ∧ Box c lx hx ly hy b) c g) :
    Relation.ReflTransGen (AdjB T m n) u (u.1 + (g.1 - c.1), u.2 + (g.2 - c.2)) := by
  induction h with
  | refl => simp only [sub_self, add_zero]; exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    rename_i b g' _
    refine ih.tail ?_
    obtain ⟨hadj, hb, hg⟩ := hab
    obtain ⟨b1, b2, b3, b4⟩ := hb
    obtain ⟨g1, g2, g3, g4⟩ := hg
    have := (adj_view hP hQ vx vy (a1 := b.1 - c.1) (b1 := b.2 - c.2) (a2 := g'.1 - c.1)
      (b2 := g'.2 - c.2) ⟨b1, b2, b3, b4⟩ ⟨g1, g2, g3, g4⟩).2
    simp only [add_sub_cancel] at this
    exact this hadj

end

end Rail
```

### `RailWalk.lean`

```lean
import RailFamily

/-!
# Boolean checkers on the reference board and their soundness

All finite facts about the reference table are stated as Boolean computations, evaluated by
the kernel in the data modules, and turned into propositions here. The checkers are generic in
the table `T`; nothing here depends on the actual data.
-/

namespace Rail

/-- Loop over `lo ≤ x < lo + k`. -/
def allZ (lo : ℤ) (f : ℤ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => f (lo + k) && allZ lo f k

lemma allZ_sound {lo : ℤ} {f : ℤ → Bool} {k : ℕ} (h : allZ lo f k = true) :
    ∀ x : ℤ, lo ≤ x → x < lo + k → f x = true := by
  induction k with
  | zero => intro x h1 h2; push_cast at h2; omega
  | succ k ih =>
    simp only [allZ, Bool.and_eq_true] at h
    intro x h1 h2
    rcases lt_or_eq_of_le (show x ≤ lo + k by push_cast at h2; omega) with h3 | h3
    · exact ih h.2 x h1 h3
    · rw [h3]; exact h.1

/-- Loop over `d < k`. -/
def allN (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => f k && allN f k

lemma allN_sound {f : ℕ → Bool} {k : ℕ} (h : allN f k = true) : ∀ d, d < k → f d = true := by
  induction k with
  | zero => intro d h; omega
  | succ k ih =>
    simp only [allN, Bool.and_eq_true] at h
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h1 | h1
    · exact ih h.2 d h1
    · rw [h1]; exact h.1

/-- Existence over `d < k`. -/
def anyN (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => f k || anyN f k

lemma anyN_sound {f : ℕ → Bool} {k : ℕ} (h : anyN f k = true) : ∃ d, d < k ∧ f d = true := by
  induction k with
  | zero => simp [anyN] at h
  | succ k ih =>
    simp only [anyN, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨k, by omega, h⟩
    · obtain ⟨d, hd, h⟩ := ih h; exact ⟨d, by omega, h⟩

/-- Count of `d < k` with `f d`. -/
def cntN (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if f k then 1 else 0) + cntN f k

def onBb (c : ℤ × ℤ) : Bool :=
  decide (0 ≤ c.1) && decide (c.1 < N0) && decide (0 ≤ c.2) && decide (c.2 < N0)

lemma onBb_iff {c : ℤ × ℤ} : onBb c = true ↔ OnB N0 N0 c := by
  simp [onBb, OnB, and_assoc]

def step (c : ℤ × ℤ) (d : ℕ) : ℤ × ℤ := (c.1 + mvx d, c.2 + mvy d)

lemma mv_inj {d e : ℕ} (hd : d < 8) (he : e < 8) (h1 : mvx d = mvx e) (h2 : mvy d = mvy e) :
    d = e := by
  interval_cases d <;> interval_cases e <;> simp_all [mvx, mvy]

section
variable (T : ℤ → ℤ → ℕ → Bool)

/-- The reference cell `c` is joined to `step c d`. -/
def adjd (c : ℤ × ℤ) (d : ℕ) : Bool :=
  onBb c && onBb (step c d) && (T c.1 c.2 d || T (c.1 + mvx d) (c.2 + mvy d) (negd d))

lemma adjd_iff {c : ℤ × ℤ} {d : ℕ} (hd : d < 8) : adjd T c d = true ↔ Adj0 T c (step c d) := by
  unfold adjd Adj0 step
  simp only [Bool.and_eq_true, Bool.or_eq_true, onBb_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, d, hd, rfl, h3⟩
  · rintro ⟨h1, h2, e, he, h4, h5⟩
    simp only [Prod.mk.injEq] at h4
    have := mv_inj hd he (by omega) (by omega)
    subst this
    exact ⟨⟨h1, h2⟩, h5⟩

/-- Boolean adjacency in the reference board. -/
def isAdj (a b : ℤ × ℤ) : Bool := anyN (fun d => decide (b = step a d) && adjd T a d) 8

lemma isAdj_sound {a b : ℤ × ℤ} (h : isAdj T a b = true) : Adj0 T a b := by
  obtain ⟨d, hd, h⟩ := anyN_sound h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1]; exact (adjd_iff T hd).1 h.2

/-- Some move from `c` along the 2-factor not leading back to `p` (any choice; soundness does
not depend on it). -/
def nextD (p c : ℤ × ℤ) : Option ℕ :=
  (List.range 8).find? (fun d => adjd T c d && !decide (step c d = p))

lemma nextD_spec {p c : ℤ × ℤ} {d : ℕ} (h : nextD T p c = some d) :
    d < 8 ∧ adjd T c d = true := by
  unfold nextD at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true] at h2
  exact ⟨List.mem_range.mp h1, h2.1⟩

/-- Walk along the 2-factor from `c` (coming from `p`) inside the window `win` until `goal`. -/
def walkB (win goal : ℤ × ℤ → Bool) : ℕ → ℤ × ℤ → ℤ × ℤ → Bool
  | 0, _, c => goal c
  | k + 1, p, c => goal c ||
      (match nextD T p c with
       | some d => win (step c d) && walkB win goal k c (step c d)
       | none => false)

lemma walkB_sound {win goal : ℤ × ℤ → Bool} {k : ℕ} {p c : ℤ × ℤ}
    (h : walkB T win goal k p c = true) (hc : win c = true) :
    ∃ g, goal g = true ∧
      Relation.ReflTransGen (fun a b => Adj0 T a b ∧ win a = true ∧ win b = true) c g := by
  induction k generalizing p c with
  | zero => exact ⟨c, h, Relation.ReflTransGen.refl⟩
  | succ k ih =>
    simp only [walkB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨c, h, Relation.ReflTransGen.refl⟩
    · split at h
      · rename_i d hd
        simp only [Bool.and_eq_true] at h
        obtain ⟨hd8, hadj⟩ := nextD_spec T hd
        obtain ⟨g, hg, hr⟩ := ih h.2 h.1
        exact ⟨g, hg, Relation.ReflTransGen.head ⟨(adjd_iff T hd8).1 hadj, hc, h.1⟩ hr⟩
      · simp at h

end

end Rail
```

### `RailInsert.lean`

```lean
import RailWalk

/-!
# Connectivity by period insertion

The board `(m + 8) × n` is obtained from `m × n` by inserting 8 columns at the cut `XC`;
the board `N0 × (n + 8)` from `N0 × n` by inserting 8 rows at the cut `YC`. Cells on either
side of the cut keep their class (`tau`), so edges not crossing the cut survive unchanged.
Two local conditions on the reference table, stated below as propositions, then give
connectivity of the bigger board from connectivity of the smaller one:
* (cross) a crossing edge is replaced by a path through the inserted strip;
* (strip) every cell of the inserted strip reaches a cell outside it.
-/

set_option linter.unnecessarySeqFocus false

namespace Rail

/-- Column cut and row cut. -/
notation "XC" => (22 : ℤ)
notation "YC" => (24 : ℤ)

section
variable (T : ℤ → ℤ → ℕ → Bool)

def Reach (m n : ℤ) (u v : ℤ × ℤ) : Prop := Relation.ReflTransGen (AdjB T m n) u v

/-- Every cell of the `m × n` board reaches the corner `(0, 0)`. -/
def Conn (m n : ℤ) : Prop := ∀ u, OnB m n u → Reach T m n u (0, 0)

/-- Reference adjacency restricted to an offset box around `c`. -/
def RW (lx hx ly hy : ℤ) (c : ℤ × ℤ) (a b : ℤ × ℤ) : Prop :=
  Adj0 T a b ∧ Box c lx hx ly hy a ∧ Box c lx hx ly hy b

/-- Column insertion, crossing condition. -/
def XCross : Prop :=
  ∀ c : ℤ × ℤ, XC - 2 ≤ c.1 → c.1 < XC → 0 ≤ c.2 → c.2 < N0 → ∀ d : ℕ, d < 8 →
    Adj0 T c (step c d) → XC ≤ (step c d).1 →
    Relation.ReflTransGen (RW T (6 - c.1) (53 - c.1) (-8) 8 c) c ((step c d).1 + 8, (step c d).2)

/-- Column insertion, strip condition. -/
def XStrip : Prop :=
  ∀ c : ℤ × ℤ, XC ≤ c.1 → c.1 < XC + 8 → 0 ≤ c.2 → c.2 < N0 →
    ∃ g : ℤ × ℤ, (g.1 < XC ∨ XC + 8 ≤ g.1) ∧
      Relation.ReflTransGen (RW T (6 - c.1) (53 - c.1) (-8) 8 c) c g

/-- Row insertion (at width `N0`), crossing condition. -/
def YCross : Prop :=
  ∀ c : ℤ × ℤ, YC - 2 ≤ c.2 → c.2 < YC → 0 ≤ c.1 → c.1 < N0 → ∀ d : ℕ, d < 8 →
    Adj0 T c (step c d) → YC ≤ (step c d).2 →
    Relation.ReflTransGen (RW T (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) c) c
      ((step c d).1, (step c d).2 + 8)

/-- Row insertion (at width `N0`), strip condition. -/
def YStrip : Prop :=
  ∀ c : ℤ × ℤ, YC ≤ c.2 → c.2 < YC + 8 → 0 ≤ c.1 → c.1 < N0 →
    ∃ g : ℤ × ℤ, (g.2 < YC ∨ YC + 8 ≤ g.2) ∧
      Relation.ReflTransGen (RW T (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) c) c g

end

/-- Insertion map on one coordinate. -/
def ins (X x : ℤ) : ℤ := if x < X then x else x + 8

lemma tau_ins {m X x : ℤ} (hm : Fam m) (hX1 : 14 ≤ X) (hX2 : X ≤ 46) (h0 : 0 ≤ x)
    (h1 : x < m) : tau (m + 8) (ins X x) = tau m x := by
  obtain ⟨t, rfl⟩ := hm
  unfold tau ins
  split_ifs <;> omega

lemma fam_add {m : ℤ} (hm : Fam m) : Fam (m + 8) := by
  obtain ⟨t, rfl⟩ := hm
  exact ⟨t + 1, by push_cast; ring⟩

section
variable {T : ℤ → ℤ → ℕ → Bool}

lemma reach_onB {m n : ℤ} {u v : ℤ × ℤ} (h : Reach T m n u v) (hu : OnB m n u) :
    OnB m n v := by
  induction h with
  | refl => exact hu
  | tail _ hab _ => exact hab.2.1

lemma reach_symm {m n : ℤ} {u v : ℤ × ℤ} (h : Reach T m n u v) : Reach T m n v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adjB_symm hab) ih

/-- The step of a board edge has knight-move size. -/
lemma adjB_step {m n : ℤ} {a b : ℤ × ℤ} (h : AdjB T m n a b) :
    ∃ d, d < 8 ∧ b = step a d := by
  obtain ⟨_, _, d, hd, rfl, _⟩ := h
  exact ⟨d, hd, rfl⟩

/-- Edges not crossing the column cut survive the insertion. -/
lemma adjB_ins_x {m n : ℤ} (hm : Fam m) {a b : ℤ × ℤ} (h : AdjB T m n a b)
    (hs : (a.1 < XC ∧ b.1 < XC) ∨ (XC ≤ a.1 ∧ XC ≤ b.1)) :
    AdjB T (m + 8) n (ins XC a.1, a.2) (ins XC b.1, b.2) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, d, hd, rfl, ht⟩ := h
  have hm60 : 60 ≤ m := by obtain ⟨t, rfl⟩ := hm; omega
  refine ⟨?_, ?_, d, hd, ?_, ?_⟩
  · unfold OnB ins; simp only; split_ifs <;> omega
  · unfold OnB ins; simp only at b1 b2 ⊢; split_ifs <;> omega
  · simp only at hs ⊢; unfold ins; ext <;> simp <;> split_ifs <;> omega
  · rw [tau_ins hm (by norm_num) (by norm_num) a1 a2,
      tau_ins hm (by norm_num) (by norm_num) b1 b2]
    exact ht

/-- Edges not crossing the row cut survive the insertion. -/
lemma adjB_ins_y {m n : ℤ} (hn : Fam n) {a b : ℤ × ℤ} (h : AdjB T m n a b)
    (hs : (a.2 < YC ∧ b.2 < YC) ∨ (YC ≤ a.2 ∧ YC ≤ b.2)) :
    AdjB T m (n + 8) (a.1, ins YC a.2) (b.1, ins YC b.2) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, d, hd, rfl, ht⟩ := h
  have hn60 : 60 ≤ n := by obtain ⟨t, rfl⟩ := hn; omega
  refine ⟨?_, ?_, d, hd, ?_, ?_⟩
  · unfold OnB ins; simp only; split_ifs <;> omega
  · unfold OnB ins; simp only at b3 b4 ⊢; split_ifs <;> omega
  · simp only at hs ⊢; unfold ins; ext <;> simp <;> split_ifs <;> omega
  · rw [tau_ins hn (by norm_num) (by norm_num) a3 a4,
      tau_ins hn (by norm_num) (by norm_num) b3 b4]
    exact ht

end

section
variable {T : ℤ → ℤ → ℕ → Bool}

lemma reach_map {m n m' n' : ℤ} (f : ℤ × ℤ → ℤ × ℤ)
    (hf : ∀ a b, OnB m n a → AdjB T m n a b → Reach T m' n' (f a) (f b))
    {a b : ℤ × ℤ} (ha : OnB m n a) (h : Reach T m n a b) : Reach T m' n' (f a) (f b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.trans (hf _ _ (reach_onB hab ha) hbc)

lemma step_eq (a : ℤ × ℤ) (d : ℕ) : step a d = (a.1 + mvx d, a.2 + mvy d) := rfl

lemma add_zero_pair (a : ℤ × ℤ) : (a.1 + 0, a.2 + 0) = a := by simp

/-- Column insertion preserves connectivity. -/
theorem conn_x (hP : PerX T) (hQ : PerY T) (hc : XCross T) (hs : XStrip T) {m n : ℤ}
    (hm : Fam m) (hn : Fam n) (h : Conn T m n) : Conn T (m + 8) n := by
  have hm8 := fam_add hm
  have hm60 : 60 ≤ m := by obtain ⟨t, rfl⟩ := hm; omega
  let f : ℤ × ℤ → ℤ × ℤ := fun a => (ins XC a.1, a.2)
  -- crossing edges
  have key : ∀ a b, AdjB T m n a b → a.1 < XC → XC ≤ b.1 → Reach T (m + 8) n (f a) (f b) := by
    intro a b hab h1 h2
    obtain ⟨d, hd, rfl⟩ := adjB_step hab
    have hon := hab.1
    obtain ⟨bx1, bx2, by1, by2⟩ := mv_bound (d := d)
    rw [step_eq] at h2
    simp only at h2
    have vx : AxView m a.1 a.1 (-2) 2 := view_left hm (by omega)
    have vy : AxView n a.2 (tau n a.2) (-8) 8 := view_anchor hn hon.2.2.1 hon.2.2.2
    have hc2 := ((vy 0 (by norm_num) (by norm_num)).1.1 ⟨by simpa using hon.2.2.1,
      by simpa using hon.2.2.2⟩)
    simp only [add_zero] at hc2
    have h0 : Adj0 T (a.1, tau n a.2) (step (a.1, tau n a.2) d) := by
      have := (adj_view hP hQ (u := a) (c := (a.1, tau n a.2)) vx vy (a1 := 0) (b1 := 0)
        (a2 := mvx d) (b2 := mvy d) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
        ⟨by omega, by omega, by omega, by omega⟩).1
      rw [add_zero_pair] at this
      simpa [step_eq] using this hab
    have hpath := hc (a.1, tau n a.2) (by simp only; omega) (by simpa using h1) hc2.1 hc2.2
      d hd h0 (by simp only [step_eq]; omega)
    have vx' : AxView (m + 8) a.1 a.1 (6 - a.1) (53 - a.1) := view_left hm8 (by omega)
    have := path_view hP hQ (u := a) (c := (a.1, tau n a.2)) vx' vy hpath
    have e1 : f a = a := by simp [f, ins, h1]
    have e2 : f (a.1 + mvx d, a.2 + mvy d) = (a.1 + mvx d + 8, a.2 + mvy d) := by
      show (ins XC (a.1 + mvx d), a.2 + mvy d) = _
      unfold ins; split_ifs <;> first | omega | rfl
    show Reach T _ _ (f a) (f (a.1 + mvx d, a.2 + mvy d))
    rw [e1, e2]
    unfold Reach
    convert this using 2
    all_goals simp [step_eq]
  have hedge : ∀ a b, OnB m n a → AdjB T m n a b → Reach T (m + 8) n (f a) (f b) := by
    intro a b _ hab
    by_cases hs1 : (a.1 < XC ∧ b.1 < XC) ∨ (XC ≤ a.1 ∧ XC ≤ b.1)
    · exact Relation.ReflTransGen.single (adjB_ins_x hm hab hs1)
    · rcases lt_or_ge a.1 XC with h1 | h1
      · exact key a b hab h1 (by omega)
      · exact reach_symm (key b a (adjB_symm hab) (by omega) h1)
  -- every cell of the new board reaches an image cell
  have hnew : ∀ v, OnB (m + 8) n v → ∃ a, OnB m n a ∧ Reach T (m + 8) n v (f a) := by
    have outside : ∀ v, OnB (m + 8) n v → (v.1 < XC ∨ XC + 8 ≤ v.1) →
        ∃ a, OnB m n a ∧ f a = v := by
      intro v hv hout
      obtain ⟨v1, v2, v3, v4⟩ := hv
      rcases hout with h1 | h1
      · refine ⟨v, ⟨v1, by omega, v3, v4⟩, ?_⟩
        simp [f, ins, h1]
      · refine ⟨(v.1 - 8, v.2), ⟨by omega, by omega, v3, v4⟩, ?_⟩
        show (ins XC (v.1 - 8), v.2) = v
        unfold ins; split_ifs <;> first | omega | (ext <;> simp)
    intro v hv
    by_cases hout : v.1 < XC ∨ XC + 8 ≤ v.1
    · obtain ⟨a, ha, rfl⟩ := outside v hv hout
      exact ⟨a, ha, Relation.ReflTransGen.refl⟩
    · obtain ⟨v1, v2, v3, v4⟩ := hv
      have vy : AxView n v.2 (tau n v.2) (-8) 8 := view_anchor hn v3 v4
      have hc2 := ((vy 0 (by norm_num) (by norm_num)).1.1 ⟨by simpa using v3, by simpa using v4⟩)
      simp only [add_zero] at hc2
      obtain ⟨g, hg, hpath⟩ := hs (v.1, tau n v.2) (by simp only; omega) (by simp only; omega)
        hc2.1 hc2.2
      have vx' : AxView (m + 8) v.1 v.1 (6 - v.1) (53 - v.1) := view_left hm8 (by omega)
      have hr := path_view hP hQ (u := v) (c := (v.1, tau n v.2)) vx' vy hpath
      simp only at hr
      have hon := reach_onB hr ⟨v1, v2, v3, v4⟩
      obtain ⟨a, ha, hfa⟩ := outside _ hon (by simp only; omega)
      exact ⟨a, ha, hfa ▸ hr⟩
  intro v hv
  obtain ⟨a, ha, hva⟩ := hnew v hv
  have := reach_map f hedge ha (h a ha)
  have e0 : f (0, 0) = (0, 0) := by simp [f, ins]
  rw [e0] at this
  exact hva.trans this

/-- Row insertion (at width `N0`) preserves connectivity. -/
theorem conn_y (hP : PerX T) (hQ : PerY T) (hc : YCross T) (hs : YStrip T) {n : ℤ}
    (hn : Fam n) (h : Conn T N0 n) : Conn T N0 (n + 8) := by
  have hn8 := fam_add hn
  have hn60 : 60 ≤ n := by obtain ⟨t, rfl⟩ := hn; omega
  let f : ℤ × ℤ → ℤ × ℤ := fun a => (a.1, ins YC a.2)
  have key : ∀ a b, AdjB T N0 n a b → a.2 < YC → YC ≤ b.2 → Reach T N0 (n + 8) (f a) (f b) := by
    intro a b hab h1 h2
    obtain ⟨d, hd, rfl⟩ := adjB_step hab
    have hon := hab.1
    obtain ⟨bx1, bx2, by1, by2⟩ := mv_bound (d := d)
    rw [step_eq] at h2
    simp only at h2
    have vx : AxView N0 a.1 a.1 (-2) 2 := view_ref
    have vy : AxView n a.2 a.2 (-2) 2 := view_left hn (by omega)
    have h0 : Adj0 T a (step a d) := by
      have := (adj_view hP hQ (u := a) (c := a) vx vy (a1 := 0) (b1 := 0)
        (a2 := mvx d) (b2 := mvy d) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
        ⟨by omega, by omega, by omega, by omega⟩).1
      rw [add_zero_pair] at this
      simpa [step_eq] using this hab
    have hpath := hc a (by omega) h1 hon.1 hon.2.1 d hd h0 (by simp only [step_eq]; omega)
    have vx' : AxView N0 a.1 a.1 (-a.1) (N0 - 1 - a.1) := view_ref
    have vy' : AxView (n + 8) a.2 a.2 (6 - a.2) (53 - a.2) := view_left hn8 (by omega)
    have := path_view hP hQ (u := a) (c := a) vx' vy' hpath
    have e1 : f a = a := by simp [f, ins, h1]
    have e2 : f (a.1 + mvx d, a.2 + mvy d) = (a.1 + mvx d, a.2 + mvy d + 8) := by
      show (a.1 + mvx d, ins YC (a.2 + mvy d)) = _
      unfold ins; split_ifs <;> first | omega | rfl
    show Reach T _ _ (f a) (f (a.1 + mvx d, a.2 + mvy d))
    rw [e1, e2]
    unfold Reach
    convert this using 2
    all_goals simp [step_eq]
  have hedge : ∀ a b, OnB N0 n a → AdjB T N0 n a b → Reach T N0 (n + 8) (f a) (f b) := by
    intro a b _ hab
    by_cases hs1 : (a.2 < YC ∧ b.2 < YC) ∨ (YC ≤ a.2 ∧ YC ≤ b.2)
    · exact Relation.ReflTransGen.single (adjB_ins_y hn hab hs1)
    · rcases lt_or_ge a.2 YC with h1 | h1
      · exact key a b hab h1 (by omega)
      · exact reach_symm (key b a (adjB_symm hab) (by omega) h1)
  have hnew : ∀ v, OnB N0 (n + 8) v → ∃ a, OnB N0 n a ∧ Reach T N0 (n + 8) v (f a) := by
    have outside : ∀ v, OnB N0 (n + 8) v → (v.2 < YC ∨ YC + 8 ≤ v.2) →
        ∃ a, OnB N0 n a ∧ f a = v := by
      intro v hv hout
      obtain ⟨v1, v2, v3, v4⟩ := hv
      rcases hout with h1 | h1
      · refine ⟨v, ⟨v1, v2, v3, by omega⟩, ?_⟩
        simp [f, ins, h1]
      · refine ⟨(v.1, v.2 - 8), ⟨v1, v2, by omega, by omega⟩, ?_⟩
        show (v.1, ins YC (v.2 - 8)) = v
        unfold ins; split_ifs <;> first | omega | (ext <;> simp)
    intro v hv
    by_cases hout : v.2 < YC ∨ YC + 8 ≤ v.2
    · obtain ⟨a, ha, rfl⟩ := outside v hv hout
      exact ⟨a, ha, Relation.ReflTransGen.refl⟩
    · obtain ⟨v1, v2, v3, v4⟩ := hv
      obtain ⟨g, hg, hpath⟩ := hs v (by omega) (by omega) v1 v2
      have vx' : AxView N0 v.1 v.1 (-v.1) (N0 - 1 - v.1) := view_ref
      have vy' : AxView (n + 8) v.2 v.2 (6 - v.2) (53 - v.2) := view_left hn8 (by omega)
      have hr := path_view hP hQ (u := v) (c := v) vx' vy' hpath
      simp only [add_sub_cancel] at hr
      have hon := reach_onB hr ⟨v1, v2, v3, v4⟩
      obtain ⟨a, ha, hfa⟩ := outside _ hon (by simp only; omega)
      exact ⟨a, ha, hfa ▸ hr⟩
  intro v hv
  obtain ⟨a, ha, hva⟩ := hnew v hv
  have := reach_map f hedge ha (h a ha)
  have e0 : f (0, 0) = (0, 0) := by simp [f, ins]
  rw [e0] at this
  exact hva.trans this

end

end Rail
```

### `RailLocal.lean`

```lean
import RailInsert
import Mathlib.Data.Finset.Card

/-!
# Local properties of every board of the family

Degree two, absence of rails (in the parallelogram form, which is all the source definition
allows), and connectivity of every board, from the reference facts.
-/

namespace Rail

section
variable (T : ℤ → ℤ → ℕ → Bool)

open Classical in
/-- The reference board is a 2-factor. -/
def Deg0 : Prop :=
  ∀ c : ℤ × ℤ, OnB N0 N0 c → ((Finset.range 8).filter (fun d => Adj0 T c (step c d))).card = 2

/-- The reference board has no parallelogram rail. -/
def NoRail0 : Prop :=
  ∀ c : ℤ × ℤ, OnB N0 N0 c → ∀ a b : ℕ, a < 8 → b < 8 →
    Adj0 T c (step c a) → Adj0 T (step c b) (step (step c b) a) →
    Adj0 T c (step c b) ∨ Adj0 T (step c a) (step (step c a) b)

/-- Descent to the corner on the reference board. -/
def Desc0 : Prop :=
  ∃ pos : ℤ × ℤ → ℕ, ∀ c : ℤ × ℤ, OnB N0 N0 c → c ≠ (0, 0) →
    ∃ d, d < 8 ∧ Adj0 T c (step c d) ∧ pos (step c d) < pos c

end

lemma fam_ref : Fam N0 := ⟨0, by norm_num⟩

section
variable {T : ℤ → ℤ → ℕ → Bool}

lemma adjB_ref (hP : PerX T) (hQ : PerY T) {u : ℤ × ℤ} {d : ℕ} :
    AdjB T N0 N0 u (step u d) ↔ Adj0 T u (step u d) := by
  obtain ⟨b1, b2, b3, b4⟩ := mv_bound (d := d)
  have := adj_view hP hQ (u := u) (c := u) view_ref view_ref (a1 := 0) (b1 := 0) (a2 := mvx d)
    (b2 := mvy d) (lx := -2) (hx := 2) (ly := -2) (hy := 2)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨by omega, by omega, by omega, by omega⟩
  simpa [step_eq] using this

lemma conn_ref (hP : PerX T) (hQ : PerY T) (h : Desc0 T) : Conn T N0 N0 := by
  obtain ⟨pos, hpos⟩ := h
  have key : ∀ k : ℕ, ∀ c : ℤ × ℤ, OnB N0 N0 c → pos c ≤ k → Reach T N0 N0 c (0, 0) := by
    intro k
    induction k with
    | zero =>
      intro c hc hk
      by_cases h0 : c = (0, 0)
      · rw [h0]; exact Relation.ReflTransGen.refl
      · obtain ⟨d, _, hadj, hlt⟩ := hpos c hc h0; omega
    | succ k ih =>
      intro c hc hk
      by_cases h0 : c = (0, 0)
      · rw [h0]; exact Relation.ReflTransGen.refl
      · obtain ⟨d, _, hadj, hlt⟩ := hpos c hc h0
        exact Relation.ReflTransGen.head ((adjB_ref hP hQ).2 hadj) (ih _ hadj.2.1 (by omega))
  exact fun c hc => key _ c hc le_rfl

/-- Every board of the family is connected. -/
theorem conn_all (hP : PerX T) (hQ : PerY T) (hxc : XCross T) (hxs : XStrip T)
    (hyc : YCross T) (hys : YStrip T) (hd : Desc0 T) (t s : ℕ) :
    Conn T (N0 + 8 * t) (N0 + 8 * s) := by
  have hy : ∀ s : ℕ, Conn T N0 (N0 + 8 * s) := by
    intro s
    induction s with
    | zero => simpa using conn_ref hP hQ hd
    | succ s ih =>
      have := conn_y hP hQ hyc hys ⟨s, rfl⟩ ih
      rwa [show N0 + 8 * (s : ℤ) + 8 = N0 + 8 * ((s + 1 : ℕ) : ℤ) by push_cast; ring] at this
  induction t with
  | zero => simpa using hy s
  | succ t ih =>
    have := conn_x hP hQ hxc hxs ⟨t, rfl⟩ ⟨s, rfl⟩ ih
    rwa [show N0 + 8 * (t : ℤ) + 8 = N0 + 8 * ((t + 1 : ℕ) : ℤ) by push_cast; ring] at this

/-- Adjacency at offsets from a board cell equals adjacency at the anchored reference cell. -/
lemma adj_anchor (hP : PerX T) (hQ : PerY T) {m n : ℤ} (hm : Fam m) (hn : Fam n)
    {u : ℤ × ℤ} (hu : OnB m n u) {a1 b1 a2 b2 : ℤ}
    (h1 : -8 ≤ a1 ∧ a1 ≤ 8 ∧ -8 ≤ b1 ∧ b1 ≤ 8) (h2 : -8 ≤ a2 ∧ a2 ≤ 8 ∧ -8 ≤ b2 ∧ b2 ≤ 8) :
    AdjB T m n (u.1 + a1, u.2 + b1) (u.1 + a2, u.2 + b2) ↔
      Adj0 T (tau m u.1 + a1, tau n u.2 + b1) (tau m u.1 + a2, tau n u.2 + b2) :=
  adj_view hP hQ (c := (tau m u.1, tau n u.2)) (view_anchor hm hu.1 hu.2.1)
    (view_anchor hn hu.2.2.1 hu.2.2.2) h1 h2

lemma onB_anchor {m n : ℤ} (hm : Fam m) (hn : Fam n) {u : ℤ × ℤ} (hu : OnB m n u) :
    OnB N0 N0 (tau m u.1, tau n u.2) := by
  have := (onB_view (c := (tau m u.1, tau n u.2)) (view_anchor hm hu.1 hu.2.1)
    (view_anchor hn hu.2.2.1 hu.2.2.2) (a := 0) (b := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).1
  simpa using this (by simpa using hu)

open Classical in
/-- Degree two on every board of the family. -/
lemma deg_board (hP : PerX T) (hQ : PerY T) (hdeg : Deg0 T) {m n : ℤ} (hm : Fam m)
    (hn : Fam n) {u : ℤ × ℤ} (hu : OnB m n u) :
    ((Finset.range 8).filter (fun d => AdjB T m n u (step u d))).card = 2 := by
  have := hdeg _ (onB_anchor hm hn hu)
  rw [← this]
  congr 1
  apply Finset.filter_congr
  intro d hd
  rw [Finset.mem_range] at hd
  obtain ⟨b1, b2, b3, b4⟩ := mv_bound (d := d)
  have := adj_anchor hP hQ hm hn hu (a1 := 0) (b1 := 0) (a2 := mvx d) (b2 := mvy d)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨by omega, by omega, by omega, by omega⟩
  simpa [step_eq] using this

/-- No parallelogram rail on any board of the family. -/
lemma norail_board (hP : PerX T) (hQ : PerY T) (hr : NoRail0 T) {m n : ℤ} (hm : Fam m)
    (hn : Fam n) {u : ℤ × ℤ} (hu : OnB m n u) {a b : ℕ} (ha : a < 8) (hb : b < 8)
    (h1 : AdjB T m n u (step u a)) (h2 : AdjB T m n (step u b) (step (step u b) a)) :
    AdjB T m n u (step u b) ∨ AdjB T m n (step u a) (step (step u a) b) := by
  obtain ⟨a1, a2, a3, a4⟩ := mv_bound (d := a)
  obtain ⟨b1, b2, b3, b4⟩ := mv_bound (d := b)
  have e := fun x1 y1 x2 y2 (h : -8 ≤ x1 ∧ x1 ≤ 8 ∧ -8 ≤ y1 ∧ y1 ≤ 8)
    (h' : -8 ≤ x2 ∧ x2 ≤ 8 ∧ -8 ≤ y2 ∧ y2 ≤ 8) => adj_anchor (T := T) hP hQ hm hn hu h h'
  have k1 := e 0 0 (mvx a) (mvy a) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by omega, by omega, by omega, by omega⟩
  have k2 := e (mvx b) (mvy b) (mvx b + mvx a) (mvy b + mvy a)
    ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
  have k3 := e 0 0 (mvx b) (mvy b) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by omega, by omega, by omega, by omega⟩
  have k4 := e (mvx a) (mvy a) (mvx a + mvx b) (mvy a + mvy b)
    ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
  simp only [add_zero, ← add_assoc] at k1 k2 k3 k4
  simp only [step_eq] at h1 h2 ⊢
  have := hr _ (onB_anchor hm hn hu) a b ha hb (by simpa [step_eq] using k1.1 h1)
    (by simpa [step_eq] using k2.1 h2)
  simp only [step_eq] at this
  rcases this with h | h
  · exact Or.inl (k3.2 (by simpa using h))
  · exact Or.inr (k4.2 (by simpa using h))

end

end Rail
```

### `RailChecks.lean`

```lean
import RailLocal

/-!
# Boolean checks for a reference table, and their soundness

`mkT R` turns a raw table `R : ℕ → ℕ → ℕ → Bool` into a reference table that is `false` off
the board and for `d ≥ 8`. Each `…b` function below is a Boolean check that the kernel can
evaluate; each `…_of` lemma turns a successful check into the proposition used by the proof.
-/

namespace Rail

def mkT (R : ℕ → ℕ → ℕ → Bool) (x y : ℤ) (d : ℕ) : Bool :=
  decide (0 ≤ x) && decide (x < N0) && decide (0 ≤ y) && decide (y < N0) && decide (d < 8) &&
    R x.toNat y.toNat d

lemma mkT_offy {R : ℕ → ℕ → ℕ → Bool} {x y : ℤ} {d : ℕ} (h : ¬ (0 ≤ y ∧ y < N0 ∧ d < 8)) :
    mkT R x y d = false := by
  unfold mkT
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

lemma mkT_offx {R : ℕ → ℕ → ℕ → Bool} {x y : ℤ} {d : ℕ} (h : ¬ (0 ≤ x ∧ x < N0 ∧ d < 8)) :
    mkT R x y d = false := by
  unfold mkT
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

lemma cntN_eq (f : ℕ → Bool) (k : ℕ) :
    cntN f k = ((Finset.range k).filter (fun d => f d = true)).card := by
  induction k with
  | zero => simp [cntN]
  | succ k ih =>
    rw [cntN, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; omega
    · simp

lemma allZ_complete {lo : ℤ} {f : ℤ → Bool} {k : ℕ}
    (h : ∀ x : ℤ, lo ≤ x → x < lo + k → f x = true) : allZ lo f k = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [allZ, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by push_cast; omega), ih (fun x h1 h2 => h x h1 (by push_cast; omega))⟩

/-- Checks are evaluated in chunks of the outer coordinate and recombined. -/
lemma allZ_append {lo : ℤ} {f : ℤ → Bool} {a b : ℕ} (h1 : allZ lo f a = true)
    (h2 : allZ (lo + a) f b = true) : allZ lo f (a + b) = true := by
  apply allZ_complete
  intro x hx1 hx2
  by_cases hx : x < lo + a
  · exact allZ_sound h1 x hx1 hx
  · exact allZ_sound h2 x (by omega) (by push_cast at hx2 ⊢; omega)

lemma allZ_chunks {f : ℤ → Bool} (s : ℕ) :
    ∀ q : ℕ, (∀ i : ℕ, i < q → allZ ((s : ℤ) * (i : ℤ)) f s = true) →
      allZ 0 f (s * q) = true := by
  intro q
  induction q with
  | zero => intro _; rfl
  | succ q ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h q (by omega)
    have := allZ_append h1 (b := s) (by simpa using h2)
    simpa [Nat.mul_succ] using this

lemma box_abs {c z : ℤ × ℤ} :
    Box c (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) z ↔
      (0 ≤ z.1 ∧ z.1 ≤ 59 ∧ 6 ≤ z.2 ∧ z.2 ≤ 53) := by
  unfold Box; omega

section
variable (R : ℕ → ℕ → ℕ → Bool)

def perXb : Bool :=
  allZ 6 (fun x => allZ 0 (fun y => allN (fun d => mkT R x y d == mkT R (x + 8) y d) 8) 60) 40

lemma perX_of (h : perXb R = true) : PerX (mkT R) := by
  intro x y d h1 h2
  by_cases hy : 0 ≤ y ∧ y < N0 ∧ d < 8
  · have h3 := allZ_sound h x h1 (by push_cast; omega)
    have h4 := allZ_sound h3 y hy.1 (by push_cast; omega)
    have h5 := allN_sound h4 d hy.2.2
    simpa using h5
  · rw [mkT_offy hy, mkT_offy hy]

def perYb : Bool :=
  allZ 0 (fun x => allZ 6 (fun y => allN (fun d => mkT R x y d == mkT R x (y + 8) d) 8) 40) 60

lemma perY_of (h : perYb R = true) : PerY (mkT R) := by
  intro x y d h1 h2
  by_cases hx : 0 ≤ x ∧ x < N0 ∧ d < 8
  · have h3 := allZ_sound h x hx.1 (by push_cast; omega)
    have h4 := allZ_sound h3 y h1 (by push_cast; omega)
    have h5 := allN_sound h4 d hx.2.2
    simpa using h5
  · rw [mkT_offx hx, mkT_offx hx]

def degF (x : ℤ) : Bool := allZ 0 (fun y => cntN (fun d => adjd (mkT R) (x, y) d) 8 == 2) 60

def degb : Bool := allZ 0 (degF R) 60

open Classical in
lemma deg_of (h : degb R = true) : Deg0 (mkT R) := by
  intro c ⟨h1, h2, h3, h4⟩
  have h5 := allZ_sound h c.1 h1 (by push_cast; omega)
  have h6 := allZ_sound h5 c.2 h3 (by push_cast; omega)
  simp only [beq_iff_eq, Prod.mk.eta] at h6
  rw [cntN_eq] at h6
  rw [← h6]
  congr 1
  apply Finset.filter_congr
  intro d hd
  rw [Finset.mem_range] at hd
  exact (adjd_iff (mkT R) hd).symm

def railF (x : ℤ) : Bool :=
  allZ 0 (fun y => allN (fun a => !adjd (mkT R) (x, y) a || allN (fun b =>
    !adjd (mkT R) (step (x, y) b) a || adjd (mkT R) (x, y) b ||
      adjd (mkT R) (step (x, y) a) b) 8) 8) 60

def railb : Bool := allZ 0 (railF R) 60

lemma rail_of (h : railb R = true) : NoRail0 (mkT R) := by
  intro c ⟨h1, h2, h3, h4⟩ a b ha hb k1 k2
  have h5 := allZ_sound h c.1 h1 (by push_cast; omega)
  have h6 := allZ_sound h5 c.2 h3 (by push_cast; omega)
  have h7 := allN_sound h6 a ha
  simp only [Prod.mk.eta] at h7
  rw [← adjd_iff (mkT R) ha] at k1
  rw [← adjd_iff (mkT R) ha] at k2
  rw [← adjd_iff (mkT R) hb, ← adjd_iff (mkT R) hb]
  simp only [k1, Bool.not_true, Bool.false_or] at h7
  have h8 := allN_sound h7 b hb
  simp only [k2, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h8
  exact h8

variable (P : ℕ → ℕ → ℕ)

def descF (x : ℤ) : Bool :=
  allZ 0 (fun y => decide ((x, y) = ((0 : ℤ), (0 : ℤ))) ||
    anyN (fun d => adjd (mkT R) (x, y) d &&
      decide (P (step (x, y) d).1.toNat (step (x, y) d).2.toNat < P x.toNat y.toNat)) 8) 60

def descb : Bool := allZ 0 (descF R P) 60

lemma desc_of (h : descb R P = true) :
    ∀ c : ℤ × ℤ, OnB N0 N0 c → c ≠ (0, 0) → ∃ d, d < 8 ∧ Adj0 (mkT R) c (step c d) ∧
      P (step c d).1.toNat (step c d).2.toNat < P c.1.toNat c.2.toNat := by
  intro c ⟨h1, h2, h3, h4⟩ hc
  have h5 := allZ_sound h c.1 h1 (by push_cast; omega)
  have h6 := allZ_sound h5 c.2 h3 (by push_cast; omega)
  simp only [Prod.mk.eta, Bool.or_eq_true, decide_eq_true_eq] at h6
  rcases h6 with h6 | h6
  · exact absurd h6 hc
  · obtain ⟨d, hd, h7⟩ := anyN_sound h6
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h7
    exact ⟨d, hd, (adjd_iff (mkT R) hd).1 h7.1, h7.2⟩

lemma desc0_of (h : descb R P = true) : Desc0 (mkT R) :=
  ⟨fun c => P c.1.toNat c.2.toNat, desc_of R P h⟩

/-- The row-strip condition follows from the descent: descending from a cell of the strip,
the first cell outside the strip is within two rows of it. -/
lemma ystrip_of (h : descb R P = true) : YStrip (mkT R) := by
  have hD := desc_of R P h
  have key : ∀ k : ℕ, ∀ c : ℤ × ℤ, YC ≤ c.2 → c.2 < YC + 8 → 0 ≤ c.1 → c.1 < N0 →
      P c.1.toNat c.2.toNat ≤ k → ∃ g : ℤ × ℤ, (g.2 < YC ∨ YC + 8 ≤ g.2) ∧
        Relation.ReflTransGen (RW (mkT R) (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) c) c g := by
    intro k
    induction k with
    | zero =>
      intro c h1 h2 h3 h4 hk
      obtain ⟨d, _, _, hlt⟩ := hD c ⟨h3, h4, by omega, by omega⟩
        (fun e => by rw [e] at h1; simp at h1)
      omega
    | succ k ih =>
      intro c h1 h2 h3 h4 hk
      obtain ⟨d, hd, hadj, hlt⟩ := hD c ⟨h3, h4, by omega, by omega⟩
        (fun e => by rw [e] at h1; simp at h1)
      obtain ⟨b1, b2, b3, b4⟩ := mv_bound (d := d)
      have hon := hadj.2.1
      have hbc : Box c (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) c := by
        rw [box_abs]; omega
      have hbs : Box c (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) (step c d) := by
        rw [box_abs]; obtain ⟨o1, o2, o3, o4⟩ := hon; simp only [step_eq] at *; omega
      by_cases hout : (step c d).2 < YC ∨ YC + 8 ≤ (step c d).2
      · exact ⟨step c d, hout, Relation.ReflTransGen.single ⟨hadj, hbc, hbs⟩⟩
      · obtain ⟨o1, o2, o3, o4⟩ := hon
        obtain ⟨g, hg, hr⟩ := ih (step c d) (by omega) (by omega) o1 o2 (by omega)
        refine ⟨g, hg, Relation.ReflTransGen.head ⟨hadj, hbc, hbs⟩ ?_⟩
        refine Relation.ReflTransGen.mono ?_ _ _ hr
        intro a b ⟨q1, q2, q3⟩
        refine ⟨q1, ?_, ?_⟩
        · rw [box_abs] at q2 ⊢; exact q2
        · rw [box_abs] at q3 ⊢; exact q3
  intro c h1 h2 h3 h4
  exact key _ c h1 h2 h3 h4 le_rfl

end

/-- The column window around `c`. -/
def winX (c z : ℤ × ℤ) : Bool :=
  decide (6 ≤ z.1) && decide (z.1 < 54) && decide (c.2 - 8 ≤ z.2) && decide (z.2 ≤ c.2 + 8)

lemma winX_box {c z : ℤ × ℤ} : winX c z = true ↔ Box c (6 - c.1) (53 - c.1) (-8) 8 z := by
  unfold winX Box; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

/-- The row window (absolute). -/
def winY (z : ℤ × ℤ) : Bool :=
  decide (0 ≤ z.1) && decide (z.1 < 60) && decide (6 ≤ z.2) && decide (z.2 < 54)

lemma winY_box {c z : ℤ × ℤ} :
    winY z = true ↔ Box c (-c.1) (N0 - 1 - c.1) (6 - c.2) (53 - c.2) z := by
  rw [box_abs]; unfold winY; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

section
variable (R : ℕ → ℕ → ℕ → Bool)

def xcrossF (y : ℤ) : Bool :=
  allZ 20 (fun x => allN (fun d =>
    !(adjd (mkT R) (x, y) d && decide (22 ≤ (step (x, y) d).1)) ||
      anyN (fun e => adjd (mkT R) (x, y) e && winX (x, y) (step (x, y) e) &&
        walkB (mkT R) (winX (x, y)) (fun z => decide (z = ((step (x, y) d).1 + 8, (step (x, y) d).2)))
          200 (x, y) (step (x, y) e)) 8) 8) 2

def xcrossb : Bool := allZ 0 (xcrossF R) 60

lemma xcross_of (h : xcrossb R = true) : XCross (mkT R) := by
  intro c h1 h2 h3 h4 d hd hadj hge
  have h5 := allZ_sound h c.2 h3 (by push_cast; omega)
  have h6 := allZ_sound h5 c.1 (by omega) (by push_cast; omega)
  have h7 := allN_sound h6 d hd
  simp only [Prod.mk.eta] at h7
  rw [← adjd_iff (mkT R) hd] at hadj
  simp only [hadj, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h7
  rcases h7 with h7 | h7
  · exact absurd hge h7
  obtain ⟨e, he, h8⟩ := anyN_sound h7
  simp only [Bool.and_eq_true] at h8
  obtain ⟨⟨hadj', hw⟩, h8⟩ := h8
  obtain ⟨g, hg, hr⟩ := walkB_sound (mkT R) h8 hw
  simp only [decide_eq_true_eq] at hg
  subst hg
  refine Relation.ReflTransGen.head ⟨(adjd_iff (mkT R) he).1 hadj', ?_, winX_box.1 hw⟩ ?_
  · unfold Box; omega
  · refine Relation.ReflTransGen.mono ?_ _ _ hr
    intro a b ⟨q1, q2, q3⟩
    exact ⟨q1, winX_box.1 q2, winX_box.1 q3⟩

def xstripF (y : ℤ) : Bool :=
  allZ 22 (fun x => anyN (fun d =>
    adjd (mkT R) (x, y) d && winX (x, y) (step (x, y) d) &&
      walkB (mkT R) (winX (x, y)) (fun z => decide (z.1 < 22) || decide (30 ≤ z.1))
        20 (x, y) (step (x, y) d)) 8) 8

def xstripb : Bool := allZ 0 (xstripF R) 60

lemma xstrip_of (h : xstripb R = true) : XStrip (mkT R) := by
  intro c h1 h2 h3 h4
  have h5 := allZ_sound h c.2 h3 (by push_cast; omega)
  have h6 := allZ_sound h5 c.1 h1 (by push_cast; omega)
  obtain ⟨d, hd, h7⟩ := anyN_sound h6
  simp only [Prod.mk.eta, Bool.and_eq_true] at h7
  obtain ⟨⟨hadj, hw⟩, h7⟩ := h7
  obtain ⟨g, hg, hr⟩ := walkB_sound (mkT R) h7 hw
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
  refine ⟨g, hg, Relation.ReflTransGen.head ⟨(adjd_iff (mkT R) hd).1 hadj, ?_, winX_box.1 hw⟩ ?_⟩
  · unfold Box; omega
  · refine Relation.ReflTransGen.mono ?_ _ _ hr
    intro a b ⟨q1, q2, q3⟩
    exact ⟨q1, winX_box.1 q2, winX_box.1 q3⟩

def ycrossF (x : ℤ) : Bool :=
  allZ 22 (fun y => allN (fun d =>
    !(adjd (mkT R) (x, y) d && decide (24 ≤ (step (x, y) d).2)) ||
      anyN (fun e => adjd (mkT R) (x, y) e && winY (step (x, y) e) &&
        walkB (mkT R) winY (fun z => decide (z = ((step (x, y) d).1, (step (x, y) d).2 + 8)))
          1000 (x, y) (step (x, y) e)) 8) 8) 2

def ycrossb : Bool := allZ 0 (ycrossF R) 60

lemma ycross_of (h : ycrossb R = true) : YCross (mkT R) := by
  intro c h1 h2 h3 h4 d hd hadj hge
  have h5 := allZ_sound h c.1 h3 (by push_cast; omega)
  have h6 := allZ_sound h5 c.2 (by omega) (by push_cast; omega)
  have h7 := allN_sound h6 d hd
  simp only [Prod.mk.eta] at h7
  rw [← adjd_iff (mkT R) hd] at hadj
  simp only [hadj, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h7
  rcases h7 with h7 | h7
  · exact absurd hge h7
  obtain ⟨e, he, h8⟩ := anyN_sound h7
  simp only [Bool.and_eq_true] at h8
  obtain ⟨⟨hadj', hw⟩, h8⟩ := h8
  obtain ⟨g, hg, hr⟩ := walkB_sound (mkT R) h8 hw
  simp only [decide_eq_true_eq] at hg
  subst hg
  refine Relation.ReflTransGen.head ⟨(adjd_iff (mkT R) he).1 hadj', ?_, winY_box.1 hw⟩ ?_
  · rw [box_abs]; omega
  · refine Relation.ReflTransGen.mono ?_ _ _ hr
    intro a b ⟨q1, q2, q3⟩
    exact ⟨q1, winY_box.1 q2, winY_box.1 q3⟩

end

end Rail
```

### `RailData.lean`

```lean
/-!
# Reference data (generated by `scripts/gen_data.py`)

`rowT y` packs the 60 cells of row `y` of the reference board, 8 bits per cell: bit `8 x + d`
is set iff the cell `(x, y)` is joined to `(x, y) + move d`. `rowP y` packs, 12 bits per cell,
the position of each cell along the Hamiltonian cycle of the reference board, starting at `(0, 0)`.
-/

namespace Rail

def rowT (y : Nat) : Nat :=
  (if y < 30 then (if y < 15 then (if y < 7 then (if y < 3 then (if y < 1 then 2344431866757670549066525394356157927583964628393077336223648896234790680380813106363948632648633646757013426963461900838190468378779183581659395 else (if y < 2 then 1172228844310248954416536402892596450842577648011315171806371823622613144546488604946630479717777658202473471283626338014020331897383103462736901 else 588764224612280320050534349019877214872134221359900213693121458758581348123897099095657652940013207049638504956960392720534736473938930942644234)) else (if y < 5 then (if y < 4 then 981703528433506093030049462943568251633891940699960009671538830003613911215525166961214520629963821695340679386683778323135876538108171526410764 else 1954190004071101997596432700373589385208527344993437300120329672555842944652064205266260370055542448971241386331820680797066868934040555341644042) else (if y < 6 then 977120234285257165213259693708442656091047176151277379032556469056196719544580820755658192910355366485030782705469202676830970965250033437475333 else 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338))) else (if y < 11 then (if y < 9 then (if y < 8 then 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196 else 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154) else (if y < 10 then 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017 else 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146)) else (if y < 13 then (if y < 12 then 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076 else 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162) else (if y < 14 then 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181 else 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338)))) else (if y < 22 then (if y < 18 then (if y < 16 then 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196 else (if y < 17 then 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154 else 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017)) else (if y < 20 then (if y < 19 then 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146 else 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076) else (if y < 21 then 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162 else 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181))) else (if y < 26 then (if y < 24 then (if y < 23 then 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338 else 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196) else (if y < 25 then 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154 else 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017)) else (if y < 28 then (if y < 27 then 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146 else 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076) else (if y < 29 then 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162 else 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181))))) else (if y < 45 then (if y < 37 then (if y < 33 then (if y < 31 then 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338 else (if y < 32 then 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196 else 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154)) else (if y < 35 then (if y < 34 then 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017 else 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146) else (if y < 36 then 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076 else 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162))) else (if y < 41 then (if y < 39 then (if y < 38 then 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181 else 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338) else (if y < 40 then 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196 else 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154)) else (if y < 43 then (if y < 42 then 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017 else 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146) else (if y < 44 then 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076 else 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162)))) else (if y < 52 then (if y < 48 then (if y < 46 then 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181 else (if y < 47 then 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741816168579338 else 1757579698169610220622877600298487665132321054634968746517999340580688709814972839960526034979230878158065149843393996700052559182102732717789196)) else (if y < 50 then (if y < 49 then 1957243888371779172805528075795229096520015795350558391315816920046495956031726685468966409921575430764650265208877254281745375646128084515718154 else 1756415644874332652676435498904241610665714582563162276889497683785456428759417457411048688459225524267339001780060640233414679089156300254315017) else (if y < 51 then 586478619166565084823949500966718133384600311102720355856726251542074702354801769522199122727002266200572434060168395864325544728993756214363146 else 975999342485462880559636537800167658814494646999566003525244483556171836328602069452847692637117968635524588472826384970193069146143536101528076))) else (if y < 56 then (if y < 54 then (if y < 53 then 1954190004082615498350217633243161857346882925916115696858026216144676452563152327347784625825348500395449827400444842623735477053354859147985162 else 977121705406835139513683821810603012359685458843752815966662601337620050664545291931344812320245499931015310869903404954759250902945670742770181) else (if y < 55 then 586477783461030823860226947738452734676889982257071271823520121243024922693967173940173774569858856508825978923234349457982240122741541286609162 else 1757579743960449851246111704905887562076606718914374469819037138314571258195247991104595204529267073125169780171432857894821768994782767424475657)) else (if y < 58 then (if y < 57 then 1176806750792803296317681734865814147396339404353943095097630686672754385163430197409352329160686757769942365545150377687571072954775092272857354 else 1756436834761402977118360970753963327181891273931393448552012703835832267460305686697414411444293735091088122463740218146611807068797784090054661) else (if y < 59 then 979359024180124839669482629890537595804925634945191440118608859964747458595038408445588190016511167380252872225654172445933384496438006529394186 else 587236947562725860644136549068331949967130960023258937744442640351138666246250279671738935452832144307528232843527519752950900085402368926553100))))))

def rowP (y : Nat) : Nat :=
  (if y < 30 then (if y < 15 then (if y < 7 then (if y < 3 then (if y < 1 then 4351911232618062484156424722640468214349542684038210388700069730092792031284971607458700348203600129197158241726676580722107536106817689888041462405130259289544572550076657871744027054883819840973809604860638587580416 else (if y < 2 then 4339697526701720486048019516206111784239287300037521872664982618859060840532981700270877267092685097646297357458098696617306233601386048954203550728540461483341622232251534499174436254144404574013993566182141138878511 else 4354603107331575993108836745504735145969300256621233889082846082910606121350501912033831953862379421208883738698370697805940653705220988654808512386637186546869901310056793935271712156140554908686269877877720609725520)) else (if y < 5 then (if y < 4 then 3970816666275056548587787840064231329905278429310139481530612438565311987582421354371287148558207599668858132894195520358365756495863143378376890902925747801182723738850124912374103850559619285839934485731269096442957 else 3974855464132368220262575817828846673298925340466097281909094028367114206064025395438327813494762031414354275801763269831334380552520447625766456011903198685896032590489008712309067327552996337788843131261962258911234) else (if y < 6 then 4323650822690152256169063288727681820456902392346313151333801378297634144964902785628206234794335125901390295640209880665911876059610536941031869051503696915595248856972012730129276306538471779001089032228604324528181 else 4319499589424219118987693055253496390846226442802788708632786006991237360451864722189864608200333951819023408811110167559472498679180601831164052765468798352752232982756151575440141246647851739632318382076244365909032))) else (if y < 11 then (if y < 9 then (if y < 8 then 4428575413759065409754219344961976213027826520127532672098814318829472895039905066601630897353281910066191062429033264828439274088277796326927216676312423476138245615175704583291830125004346750003926518465606260583467 else 4365279211939203967588896958659315972720895921270396175765256815162890156861184230516649048050344161450058627437984464774439114955871500239488580312595997618813622718352923952914099409664103151465002224220246122716218) else (if y < 10 then 3981615066640534299861754034649606727177288493359063627752357593591117944406488692354845349032376148066264603223952244363959740629516546882282115972867743593244575667018441555059803741140508011954164941659304974360631 else 3956014313710294101578858636577591369933808777499789375503264011071796526766529692171884280513370696345086540061328123369907216678002088915589011234244541192463352178210349005607140720962216887728064949108470102249478)) else (if y < 13 then (if y < 12 then 4425882884911614032269984756830080140921801676240876682655579237538286416986948601860514832970068212591307058375159940470437470779352036569659402801298390275355278471578710897003898854121766903589916884644543772986371 else 4421949289766608179516274942719444999041197652624002314853169007147769880938968524264535002580630495230966757976752649016874827883123376933663398899685043780355650754124429118721354604521215200751750125930377583565860) else (if y < 14 then 3984188615420635011266801549368262975928731943263963375718618360771513407277880644880390883317383788270139114890089819725629409885735610849379820464055135267721657418679551533038956380111251207148650261490227665485885 else 4416564199462742798858105963325427493619308254433514906793053804509509484046052196046383003381038584649044906439905726251665662350072960722233447320346709819552796248916393149768688096456835331203071740757705853631048)))) else (if y < 22 then (if y < 18 then (if y < 16 then 3935563886872525455347458756898980784505971188181453696860511709225832752979699709939445429144641184623204499615043393887914788258090779768116315227126699933486222286105956622531037367115261823741366481811671928269387 else (if y < 17 then 3872399845959586841714040621097296543407244241817844736257151323319948672269497195952868641926734043334106999685249651835667397468473490354503129689665626185879052482483949921801555778533603466067616091913492159928926 else 3335129234860758983240501338645486575500918611621002024302562106295527433126938203409677573459184093573964328265224405490232350982706240472774022513816499190203183965999627019324051532296039912910772294462001366835263)) else (if y < 20 then (if y < 19 then 3848166398728573026611898837679170081884805222277039818840942738337681408981440315326984212514699189584218187465922548327657889549600789339805463497284930781948976723945877140218611550795651853548937835547669679070240 else 3932871358019547629901297209438543404561733441268079189563418751450786896889584409225367732383199836233046596121690957573104078686210458315716406026494550978066675373592066151571664907375607113020536878124207087815203) else (if y < 21 then 3928975241340763182918258040613503395216283634568994709915006736337326958186987161356093534293387354405808984281734138212802461055353550369081722684334809447834716253848005566909036202422292435469047050911275228273220 else 3337667912445731612386364587602294851738634772511673706568336866594754608950516015297521273799180066730424598738079206803475119467416345095000386866886618432887536339286574270956831178537616509972963534443493957517381))) else (if y < 26 then (if y < 24 then (if y < 23 then 3923590141886881127689984471832876129873989190200822181711253985382857937213010678525646324508113126181195166453825900323559139810227791912389196893516306489847389795513110103971835717861450660270194753649545019160688 else 3299815933714005796006809254115094660606856600032402422367632082298519913737337345454656529453375602491986535745449766579909863045154419568989430347783745729473520763285637972760450444327574504193287343628711293642867) else (if y < 25 then 3236651892801067182373391118311608799444599702748693813041641883756079105758085750995426023876067949693680511344289808283663144892592747581647640403109117408866625096198572303179985518324999377388595886679027228088454 else 2699381281702239323899851835859798831538274072551851101087052666731657866615526758452234955408517999933537839924264561938228098406825497699918533227259990413190756579714980151477590580580023872804958785448804387954759)) else (if y < 28 then (if y < 27 then 3212418445570053367271249334893482337922160683207888895625433298773811842470028870369541594464033095943791699124962704775653636973720046566949974210728422004936549334668074919162017565564369399363488652030389183240768 else 3297123404861027970560647706652855660599088902198928266347909311886917330378172964267925114332533742592620107780731114021099826110329715542860916739938042201004031173424325837658063146820328981615496170979830117206091) else (if y < 29 then 3293227288182243523577608537827815651253639095499843786699497296773457391675575716398650916242721260765382495940774294660798208479472807596226233397778300670822288867562627948287465942213688346790026845709803698362476 else 2701919959287211953045715084816607107775990233442522783352827427030885042439104570340078655748513973089998110397119363251470866891535602322144897580330109450187039287851172133739222407153421172325290294413038331740237))))) else (if y < 45 then (if y < 37 then (if y < 33 then (if y < 31 then 3287842188728361468349334969047188385911344651131671258495744545818988370701599233568203706457447032540768678112866056771554887234347049139533707606959797712834962406235307882915241732630168206084745570132264523331224 else (if y < 32 then 2664067980555486136666159751329406916644212060963251499152122642734650347225925900497213911402709508851560047404489923027905610469273676796133941061227236952410876563117897658846848686368444802055107048427371335313051 else 2600903939642547523032741615525921055481955163679542889826132444192209539246674306037983405825401856053254023003329964731658892316712004808792151116552608631854197709913925435377080709575497285906217665489881786652334)) else (if y < 35 then (if y < 34 then 2063633328543719664559202333074111087575629533482700177871543227167788300104115313494792337357851906293111351583304718386223845830944754927063043940703481636178329193430333283674685771830521781322580564259658946519119 else 2576670492411533707930599832107794593959516144138737972409923859209942275958617425412098976413367002303365210784002861223649384397839303794094484924171913227924121948383428051359112756814867307881110430841243741804648) else (if y < 36 then 2661375451702508311219998203867167916636444363129777343132399872323047763866761519310482496281867648952193619439771270469095573534448972770005427453381533423991603787139678969855158338070826890133671352112895964284531 else 2657479335023723864236959035042127907290994556430692863483987857209587825164164271441208298192055167124956007599814451108793955903592064823370744111221791893809861481277981080484561133464186255307648624553651658823316))) else (if y < 41 then (if y < 39 then (if y < 38 then 2066172006128692293705065582030919363813345694373371860137317987467015475927693125382636037697847879449571622056159519699466614315654859549289408293773600673174611901566525265936317598403919080842912208331881711419477 else 2652094235569841809008685466261500641948700112062520335280235106255118804190187788610761088406780938900342189771906213219550634658466306366678218320403288935822535019950661015112336923880666114602367348943119081895104) else (if y < 40 then 2028320027396966477325510248543719172681567521894100575936613203170780780714514455539771293352043415211133559063530079475901357893392934023278451774670728175398449176833250791043943877618942710572728827238225895843011 else 1965155986484026036178982082364439817737242147760082054098869941269523370857336372386117004207289043541687648678590201203806767951296796493121458153796080565403528817558840425265646044816410476347819992027874932102358)) else (if y < 43 then (if y < 42 then 1427885375385200005218443875424861757811048398468273353359737070919354648817966042269501299525625965177528316235251928232329314503919440032945497173967426299635497763014946574974143391991615603340076773782081747132503 else 1940922539245528554891265910078448949081591633280841509773249677864894955604754488063137539264285275486719103693846889357339140795506923123840847405260466725316373359919879230836020119000931983647334595329744656127632) else (if y < 44 then 2025627498543988651879239746217918586871863251181808859129854460974995711580911709369413957634925606071983491192973360856014826157830202161738267900100186275477392384122105519254948528447406856908359182742634291889307 else 2021731381865202377383199501880648254661228853050542179496529284310461343529287054400237694915042296442763593005986612269034529331826274599292736665366731502306903396221063683159313100239227903120699850501276253983932)))) else (if y < 52 then (if y < 48 then (if y < 46 then 1430424052970172634364307124381670034048764582425403376134772576118963423641843315441567499050905836569361493809361610086385866939036088941022248740492253524660400498548951815336107788780499047617046771747397571625053 else (if y < 47 then 2016346282403834828456241513856363089177636344761074946906640992712521384966157155700054329995386175247901530432657105403711824822843433625129598133168340363487413794632467723471581816782453303324846863318295379964648 else 1392446488493797350567266412261016079845096395583339688658172270366167962448480802794074790916547744906650386598350728607872712177829190276694060044811731713228945092850529148828952242023303189141988403419367745118955)) else (if y < 50 then (if y < 49 then 1329408033318025418433963080734429516743226490246993463531071773769582232888867369983338705569323638965541207265695043797004994324433329875255551555087036424552729319328209148513363983044151684133049376602881430098686 else 277738212142461803453831140469869429183085446339727191593792542432748053616916812969163712382918222540978407485279363671930494074131707863009198851532684143385924250055015483514008017978387188504874408366125129941087) else (if y < 51 then 1305174586105583633551518995344406348315773065475814999595516046377599296827672730788478758167337590341632910469864878373249553675828000394010150885389504742270759900004385001575590000531903846307959769785150596863160 else 1389753959640817869388461422445483027445870308770256784779298579802361368709356794560811055277772974808386869553754903867499534415006556491567977031165230571305002185410842755041467606643177777804943501871511773774149))) else (if y < 56 then (if y < 54 then (if y < 53 then 1385983428699201759638157685541320840034158675871343169194866502664333456665973024742846515194522991809711121933138946187864913046410159099300713448180391926322218957989548662394668363136204920113830817841337179878116 else 280151303982783137669098980416106313991179745725453288334964267900636625346266374261589209257194617110257805719933647626520473317923052802844196266553636552387828460982635776758441884507801911340738379603606641131621) else (if y < 55 then 1380598298603314080016763598528910424926616862805806024736607238333822067167812935440804906287757835285072452619141452348515694282969473882682119283672866191952668786362568995525215598783949131174392923931116253352268 else 242610960691001578191228119307140890435620586434679586393368514719122856338779525689844406891345016013880071434726335516370453496356165031331556724811989194434888698384189970502599119253152936475848250473477950562645)) else (if y < 58 then (if y < 57 then 230325584138006755288047069658902104317111856651918141981462241060165867536047211778402297716213697462689192971070287123798023848091240280714668580314399519548329974254434643712311119116125085244438305762750741451104 else 918436508741684671785177153004569887399932341257632435124407622575425381078217234544088847935807338237860146078732539386615724487810973234008156853287064608620843067571237931215074531898777082409638068946359662502243) else (if y < 59 then 235709334036344725927541166374071364754007690322148163209098250253451052876923583800792626852642277211894889638839183854628007464062689769519691341378581409153979891842756364368204392525943407936763041352411818348890 else 239918428782182151522682919310526734674540834144370923763511674315069997495563695147164842329963061003348817418181869195368069442263177480727865966296231991684874901012846278494474761724253251043933435474631575617879))))))

def rawT (x y d : Nat) : Bool := (rowT y >>> (8 * x + d)) % 2 == 1

def rawP (x y : Nat) : Nat := (rowP y >>> (12 * x)) % 4096

end Rail
```

### `RailRunMisc.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem perX_ok : perXb rawT = true := by decide +kernel

theorem perY_ok : perYb rawT = true := by decide +kernel

end Rail
```

### `RailRunDeg0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem deg_c0 : allZ ((5 : ℕ) * ((0 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c1 : allZ ((5 : ℕ) * ((1 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c2 : allZ ((5 : ℕ) * ((2 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c3 : allZ ((5 : ℕ) * ((3 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c4 : allZ ((5 : ℕ) * ((4 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c5 : allZ ((5 : ℕ) * ((5 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c6 : allZ ((5 : ℕ) * ((6 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c7 : allZ ((5 : ℕ) * ((7 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c8 : allZ ((5 : ℕ) * ((8 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c9 : allZ ((5 : ℕ) * ((9 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c10 : allZ ((5 : ℕ) * ((10 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel
theorem deg_c11 : allZ ((5 : ℕ) * ((11 : ℕ) : ℤ)) (degF rawT) 5 = true := by
  decide +kernel

end Rail
```

### `RailRunDeg.lean`

```lean
import RailRunDeg0

namespace Rail

theorem deg_ok : degb rawT = true := allZ_chunks 5 12 (fun i hi => by interval_cases i; exacts [deg_c0, deg_c1, deg_c2, deg_c3, deg_c4, deg_c5, deg_c6, deg_c7, deg_c8, deg_c9, deg_c10, deg_c11])

end Rail
```

### `RailRunRail0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem rail_c0 : allZ ((2 : ℕ) * ((0 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c1 : allZ ((2 : ℕ) * ((1 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c2 : allZ ((2 : ℕ) * ((2 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c3 : allZ ((2 : ℕ) * ((3 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c4 : allZ ((2 : ℕ) * ((4 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c5 : allZ ((2 : ℕ) * ((5 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c6 : allZ ((2 : ℕ) * ((6 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c7 : allZ ((2 : ℕ) * ((7 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c8 : allZ ((2 : ℕ) * ((8 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c9 : allZ ((2 : ℕ) * ((9 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel

end Rail
```

### `RailRunRail1.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem rail_c10 : allZ ((2 : ℕ) * ((10 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c11 : allZ ((2 : ℕ) * ((11 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c12 : allZ ((2 : ℕ) * ((12 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c13 : allZ ((2 : ℕ) * ((13 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c14 : allZ ((2 : ℕ) * ((14 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c15 : allZ ((2 : ℕ) * ((15 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c16 : allZ ((2 : ℕ) * ((16 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c17 : allZ ((2 : ℕ) * ((17 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c18 : allZ ((2 : ℕ) * ((18 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c19 : allZ ((2 : ℕ) * ((19 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel

end Rail
```

### `RailRunRail2.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem rail_c20 : allZ ((2 : ℕ) * ((20 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c21 : allZ ((2 : ℕ) * ((21 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c22 : allZ ((2 : ℕ) * ((22 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c23 : allZ ((2 : ℕ) * ((23 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c24 : allZ ((2 : ℕ) * ((24 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c25 : allZ ((2 : ℕ) * ((25 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c26 : allZ ((2 : ℕ) * ((26 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c27 : allZ ((2 : ℕ) * ((27 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c28 : allZ ((2 : ℕ) * ((28 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel
theorem rail_c29 : allZ ((2 : ℕ) * ((29 : ℕ) : ℤ)) (railF rawT) 2 = true := by
  decide +kernel

end Rail
```

### `RailRunRail.lean`

```lean
import RailRunRail0
import RailRunRail1
import RailRunRail2

namespace Rail

theorem rail_ok : railb rawT = true := allZ_chunks 2 30 (fun i hi => by interval_cases i; exacts [rail_c0, rail_c1, rail_c2, rail_c3, rail_c4, rail_c5, rail_c6, rail_c7, rail_c8, rail_c9, rail_c10, rail_c11, rail_c12, rail_c13, rail_c14, rail_c15, rail_c16, rail_c17, rail_c18, rail_c19, rail_c20, rail_c21, rail_c22, rail_c23, rail_c24, rail_c25, rail_c26, rail_c27, rail_c28, rail_c29])

end Rail
```

### `RailRunDesc0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem desc_c0 : allZ ((5 : ℕ) * ((0 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c1 : allZ ((5 : ℕ) * ((1 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c2 : allZ ((5 : ℕ) * ((2 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c3 : allZ ((5 : ℕ) * ((3 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c4 : allZ ((5 : ℕ) * ((4 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c5 : allZ ((5 : ℕ) * ((5 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c6 : allZ ((5 : ℕ) * ((6 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c7 : allZ ((5 : ℕ) * ((7 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c8 : allZ ((5 : ℕ) * ((8 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c9 : allZ ((5 : ℕ) * ((9 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c10 : allZ ((5 : ℕ) * ((10 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel
theorem desc_c11 : allZ ((5 : ℕ) * ((11 : ℕ) : ℤ)) (descF rawT rawP) 5 = true := by
  decide +kernel

end Rail
```

### `RailRunDesc.lean`

```lean
import RailRunDesc0

namespace Rail

theorem desc_ok : descb rawT rawP = true := allZ_chunks 5 12 (fun i hi => by interval_cases i; exacts [desc_c0, desc_c1, desc_c2, desc_c3, desc_c4, desc_c5, desc_c6, desc_c7, desc_c8, desc_c9, desc_c10, desc_c11])

end Rail
```

### `RailRunXcross0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem xcross_c0 : allZ ((5 : ℕ) * ((0 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c1 : allZ ((5 : ℕ) * ((1 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c2 : allZ ((5 : ℕ) * ((2 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c3 : allZ ((5 : ℕ) * ((3 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c4 : allZ ((5 : ℕ) * ((4 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c5 : allZ ((5 : ℕ) * ((5 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel

end Rail
```

### `RailRunXcross1.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem xcross_c6 : allZ ((5 : ℕ) * ((6 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c7 : allZ ((5 : ℕ) * ((7 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c8 : allZ ((5 : ℕ) * ((8 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c9 : allZ ((5 : ℕ) * ((9 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c10 : allZ ((5 : ℕ) * ((10 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel
theorem xcross_c11 : allZ ((5 : ℕ) * ((11 : ℕ) : ℤ)) (xcrossF rawT) 5 = true := by
  decide +kernel

end Rail
```

### `RailRunXcross.lean`

```lean
import RailRunXcross0
import RailRunXcross1

namespace Rail

theorem xcross_ok : xcrossb rawT = true := allZ_chunks 5 12 (fun i hi => by interval_cases i; exacts [xcross_c0, xcross_c1, xcross_c2, xcross_c3, xcross_c4, xcross_c5, xcross_c6, xcross_c7, xcross_c8, xcross_c9, xcross_c10, xcross_c11])

end Rail
```

### `RailRunXstrip0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem xstrip_c0 : allZ ((5 : ℕ) * ((0 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c1 : allZ ((5 : ℕ) * ((1 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c2 : allZ ((5 : ℕ) * ((2 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c3 : allZ ((5 : ℕ) * ((3 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c4 : allZ ((5 : ℕ) * ((4 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c5 : allZ ((5 : ℕ) * ((5 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c6 : allZ ((5 : ℕ) * ((6 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c7 : allZ ((5 : ℕ) * ((7 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c8 : allZ ((5 : ℕ) * ((8 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c9 : allZ ((5 : ℕ) * ((9 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c10 : allZ ((5 : ℕ) * ((10 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel
theorem xstrip_c11 : allZ ((5 : ℕ) * ((11 : ℕ) : ℤ)) (xstripF rawT) 5 = true := by
  decide +kernel

end Rail
```

### `RailRunXstrip.lean`

```lean
import RailRunXstrip0

namespace Rail

theorem xstrip_ok : xstripb rawT = true := allZ_chunks 5 12 (fun i hi => by interval_cases i; exacts [xstrip_c0, xstrip_c1, xstrip_c2, xstrip_c3, xstrip_c4, xstrip_c5, xstrip_c6, xstrip_c7, xstrip_c8, xstrip_c9, xstrip_c10, xstrip_c11])

end Rail
```

### `RailRunYcross0.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem ycross_c0 : allZ ((1 : ℕ) * ((0 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c1 : allZ ((1 : ℕ) * ((1 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c2 : allZ ((1 : ℕ) * ((2 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c3 : allZ ((1 : ℕ) * ((3 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c4 : allZ ((1 : ℕ) * ((4 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c5 : allZ ((1 : ℕ) * ((5 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c6 : allZ ((1 : ℕ) * ((6 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c7 : allZ ((1 : ℕ) * ((7 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c8 : allZ ((1 : ℕ) * ((8 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c9 : allZ ((1 : ℕ) * ((9 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c10 : allZ ((1 : ℕ) * ((10 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c11 : allZ ((1 : ℕ) * ((11 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c12 : allZ ((1 : ℕ) * ((12 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c13 : allZ ((1 : ℕ) * ((13 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c14 : allZ ((1 : ℕ) * ((14 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c15 : allZ ((1 : ℕ) * ((15 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c16 : allZ ((1 : ℕ) * ((16 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c17 : allZ ((1 : ℕ) * ((17 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c18 : allZ ((1 : ℕ) * ((18 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c19 : allZ ((1 : ℕ) * ((19 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel

end Rail
```

### `RailRunYcross1.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem ycross_c20 : allZ ((1 : ℕ) * ((20 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c21 : allZ ((1 : ℕ) * ((21 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c22 : allZ ((1 : ℕ) * ((22 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c23 : allZ ((1 : ℕ) * ((23 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c24 : allZ ((1 : ℕ) * ((24 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c25 : allZ ((1 : ℕ) * ((25 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c26 : allZ ((1 : ℕ) * ((26 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c27 : allZ ((1 : ℕ) * ((27 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c28 : allZ ((1 : ℕ) * ((28 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c29 : allZ ((1 : ℕ) * ((29 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c30 : allZ ((1 : ℕ) * ((30 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c31 : allZ ((1 : ℕ) * ((31 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c32 : allZ ((1 : ℕ) * ((32 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c33 : allZ ((1 : ℕ) * ((33 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c34 : allZ ((1 : ℕ) * ((34 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c35 : allZ ((1 : ℕ) * ((35 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c36 : allZ ((1 : ℕ) * ((36 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c37 : allZ ((1 : ℕ) * ((37 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c38 : allZ ((1 : ℕ) * ((38 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c39 : allZ ((1 : ℕ) * ((39 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel

end Rail
```

### `RailRunYcross2.lean`

```lean
import RailChecks
import RailData

namespace Rail

theorem ycross_c40 : allZ ((1 : ℕ) * ((40 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c41 : allZ ((1 : ℕ) * ((41 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c42 : allZ ((1 : ℕ) * ((42 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c43 : allZ ((1 : ℕ) * ((43 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c44 : allZ ((1 : ℕ) * ((44 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c45 : allZ ((1 : ℕ) * ((45 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c46 : allZ ((1 : ℕ) * ((46 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c47 : allZ ((1 : ℕ) * ((47 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c48 : allZ ((1 : ℕ) * ((48 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c49 : allZ ((1 : ℕ) * ((49 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c50 : allZ ((1 : ℕ) * ((50 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c51 : allZ ((1 : ℕ) * ((51 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c52 : allZ ((1 : ℕ) * ((52 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c53 : allZ ((1 : ℕ) * ((53 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c54 : allZ ((1 : ℕ) * ((54 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c55 : allZ ((1 : ℕ) * ((55 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c56 : allZ ((1 : ℕ) * ((56 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c57 : allZ ((1 : ℕ) * ((57 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c58 : allZ ((1 : ℕ) * ((58 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel
theorem ycross_c59 : allZ ((1 : ℕ) * ((59 : ℕ) : ℤ)) (ycrossF rawT) 1 = true := by
  decide +kernel

end Rail
```

### `RailRunYcross.lean`

```lean
import RailRunYcross0
import RailRunYcross1
import RailRunYcross2

namespace Rail

theorem ycross_ok : ycrossb rawT = true := allZ_chunks 1 60 (fun i hi => by interval_cases i; exacts [ycross_c0, ycross_c1, ycross_c2, ycross_c3, ycross_c4, ycross_c5, ycross_c6, ycross_c7, ycross_c8, ycross_c9, ycross_c10, ycross_c11, ycross_c12, ycross_c13, ycross_c14, ycross_c15, ycross_c16, ycross_c17, ycross_c18, ycross_c19, ycross_c20, ycross_c21, ycross_c22, ycross_c23, ycross_c24, ycross_c25, ycross_c26, ycross_c27, ycross_c28, ycross_c29, ycross_c30, ycross_c31, ycross_c32, ycross_c33, ycross_c34, ycross_c35, ycross_c36, ycross_c37, ycross_c38, ycross_c39, ycross_c40, ycross_c41, ycross_c42, ycross_c43, ycross_c44, ycross_c45, ycross_c46, ycross_c47, ycross_c48, ycross_c49, ycross_c50, ycross_c51, ycross_c52, ycross_c53, ycross_c54, ycross_c55, ycross_c56, ycross_c57, ycross_c58, ycross_c59])

end Rail
```

### `RailAssemble.lean`

```lean
import RailStatement
import RailChecks
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-!
# From the board relation to closed knight's tours without rails

For a reference table satisfying the finite checks, the board of side `n = 60 + 8 t` carries
a subgraph of the knight's graph that is 2-regular and connected. Mathlib then gives a
Hamiltonian cycle walk, whose edge set is the whole subgraph, and that subgraph has no rail.
-/

namespace Rail

open SimpleGraph

/-- Integer coordinates of a cell. -/
def emb {n : ℕ} (a : Fin n × Fin n) : ℤ × ℤ := (((a.1 : ℕ) : ℤ), ((a.2 : ℕ) : ℤ))

lemma emb_onB {n : ℕ} (a : Fin n × Fin n) : OnB n n (emb a) := by
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [emb] <;> omega

lemma emb_inj {n : ℕ} {a b : Fin n × Fin n} (h : emb a = emb b) : a = b := by
  simp only [emb, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The cell with given integer coordinates. -/
def ofZ {n : ℕ} (u : ℤ × ℤ) (h : OnB n n u) : Fin n × Fin n :=
  (⟨u.1.toNat, by obtain ⟨h1, h2, h3, h4⟩ := h; omega⟩,
   ⟨u.2.toNat, by obtain ⟨h1, h2, h3, h4⟩ := h; omega⟩)

lemma emb_ofZ {n : ℕ} {u : ℤ × ℤ} (h : OnB n n u) : emb (ofZ u h) = u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [emb, ofZ]
  ext <;> simp <;> omega

lemma ofZ_emb {n : ℕ} (a : Fin n × Fin n) : ofZ (emb a) (emb_onB a) = a :=
  emb_inj (emb_ofZ _)

/-- A Boolean form of the fact that two knight moves summing like a 4-cycle form a
parallelogram (or degenerate). -/
def paraB : Bool :=
  allN (fun a => allN (fun b => allN (fun c => allN (fun e =>
    !(decide (mvx a + mvx c = mvx b + mvx e) && decide (mvy a + mvy c = mvy b + mvy e)) ||
      decide (b = a) || (decide (c = b) && decide (e = a)) ||
      (decide (mvx c = -mvx a) && decide (mvy c = -mvy a))) 8) 8) 8) 8

theorem paraB_ok : paraB = true := by decide

lemma para {a b c e : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8) (he : e < 8)
    (hx : mvx a + mvx c = mvx b + mvx e) (hy : mvy a + mvy c = mvy b + mvy e) :
    b = a ∨ (c = b ∧ e = a) ∨ (mvx c = -mvx a ∧ mvy c = -mvy a) := by
  have := allN_sound (allN_sound (allN_sound (allN_sound paraB_ok a ha) b hb) c hc) e he
  simp only [hx, hy, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  tauto

lemma knight_step {n : ℕ} {x y : Fin n × Fin n} (h : (knightGraph n).Adj x y) :
    ∃ b, b < 8 ∧ emb y = step (emb x) b := by
  change KnightAdj n x y at h
  unfold KnightAdj at h
  have e1 := Int.natAbs_eq (((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ))
  have e2 := Int.natAbs_eq (((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ))
  have key : ∀ dx dy : ℤ, ((y.1 : ℕ) : ℤ) = (x.1 : ℕ) + dx → ((y.2 : ℕ) : ℤ) = (x.2 : ℕ) + dy →
      ∀ b, b < 8 → mvx b = dx → mvy b = dy → ∃ b, b < 8 ∧ emb y = step (emb x) b := by
    intro dx dy hx hy b hb h1 h2
    exact ⟨b, hb, by simp only [emb, step, h1, h2, hx, hy]⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at e1 <;> rw [h2] at e2 <;>
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> push_cast at e1 e2
  · exact key (-1) (-2) (by omega) (by omega) 4 (by norm_num) rfl rfl
  · exact key (-1) 2 (by omega) (by omega) 7 (by norm_num) rfl rfl
  · exact key 1 (-2) (by omega) (by omega) 3 (by norm_num) rfl rfl
  · exact key 1 2 (by omega) (by omega) 0 (by norm_num) rfl rfl
  · exact key (-2) (-1) (by omega) (by omega) 5 (by norm_num) rfl rfl
  · exact key (-2) 1 (by omega) (by omega) 6 (by norm_num) rfl rfl
  · exact key 2 (-1) (by omega) (by omega) 2 (by norm_num) rfl rfl
  · exact key 2 1 (by omega) (by omega) 1 (by norm_num) rfl rfl

section
variable (T : ℤ → ℤ → ℕ → Bool)

/-- The tour graph on the `n × n` board. -/
def G (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj a b := AdjB T n n (emb a) (emb b)
  symm := ⟨fun _ _ h => adjB_symm h⟩
  loopless := ⟨fun a h => by
    obtain ⟨d, hd, he⟩ := adjB_step h
    simp only [step, Prod.ext_iff] at he
    have h1 : mvx d = 0 := by omega
    have h2 : mvy d = 0 := by omega
    interval_cases d <;> simp [mvx] at h1⟩

noncomputable instance (n : ℕ) : DecidableRel (G T n).Adj := Classical.decRel _

variable {T}

lemma G_le (n : ℕ) : G T n ≤ knightGraph n := by
  intro a b h
  obtain ⟨d, hd, he⟩ := adjB_step h
  simp only [emb, step, Prod.ext_iff] at he
  change KnightAdj n a b
  unfold KnightAdj
  rw [show ((a.1 : ℤ) - b.1) = - mvx d by omega,
    show ((a.2 : ℤ) - b.2) = - mvy d by omega]
  interval_cases d <;> simp [mvx, mvy]

lemma G_adj_iff {n : ℕ} {a b : Fin n × Fin n} : (G T n).Adj a b ↔ AdjB T n n (emb a) (emb b) :=
  Iff.rfl

lemma fam_n (t : ℕ) : Fam ((60 + 8 * t : ℕ) : ℤ) := ⟨t, by push_cast; ring⟩

lemma reach_G {n : ℕ} (a : Fin n × Fin n) {u : ℤ × ℤ}
    (h : Relation.ReflTransGen (AdjB T n n) (emb a) u) (hu : OnB n n u) :
    (G T n).Reachable a (ofZ u hu) := by
  induction h with
  | refl => rw [ofZ_emb]
  | tail hab hbc ih =>
    rename_i b c
    have hb := hbc.1
    refine (ih hb).trans (Adj.reachable ?_)
    rw [G_adj_iff, emb_ofZ, emb_ofZ]
    exact hbc

variable (hP : PerX T) (hQ : PerY T)
include hP hQ

open Classical in
lemma degree_G (hdeg : Deg0 T) (t : ℕ) (v : Fin (60 + 8 * t) × Fin (60 + 8 * t)) :
    (G T (60 + 8 * t)).degree v = 2 := by
  have hD := deg_board hP hQ hdeg (fam_n t) (fam_n t) (emb_onB v)
  rw [← card_neighborFinset_eq_degree, ← hD]
  symm
  refine Finset.card_bij (fun d hd => ofZ (step (emb v) d) (Finset.mem_filter.1 hd).2.2.1)
    ?_ ?_ ?_
  · intro d hd
    rw [mem_neighborFinset, G_adj_iff, emb_ofZ]
    exact (Finset.mem_filter.1 hd).2
  · intro d1 h1 d2 h2 he
    have := congrArg emb he
    rw [emb_ofZ, emb_ofZ] at this
    simp only [step, Prod.mk.injEq, add_right_inj] at this
    exact mv_inj (Finset.mem_range.1 (Finset.mem_filter.1 h1).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 h2).1) this.1 this.2
  · intro w hw
    rw [mem_neighborFinset, G_adj_iff] at hw
    obtain ⟨d, hd, he⟩ := adjB_step hw
    refine ⟨d, Finset.mem_filter.2 ⟨Finset.mem_range.2 hd, he ▸ hw⟩, emb_inj ?_⟩
    rw [emb_ofZ, he]

lemma connected_G (hxc : XCross T) (hxs : XStrip T) (hyc : YCross T) (hys : YStrip T)
    (hd : Desc0 T) (t : ℕ) : (G T (60 + 8 * t)).Connected := by
  have hc := conn_all hP hQ hxc hxs hyc hys hd t t
  have h00 : OnB ((60 + 8 * t : ℕ) : ℤ) ((60 + 8 * t : ℕ) : ℤ) (0, 0) := by
    refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> push_cast <;> omega
  rw [connected_iff_exists_forall_reachable]
  refine ⟨ofZ (0, 0) h00, fun w => ?_⟩
  have := hc (emb w) (by simpa using emb_onB w)
  exact (reach_G w (by simpa [Reach] using this) h00).symm

lemma isCycles_G (hdeg : Deg0 T) (t : ℕ) : (G T (60 + 8 * t)).IsCycles := by
  intro v _
  rw [Set.ncard_eq_toFinset_card', ← neighborFinset_def, card_neighborFinset_eq_degree,
    degree_G hP hQ hdeg]

/-- A Hamiltonian cycle of the tour graph. -/
lemma exists_ham_G (hdeg : Deg0 T) (hxc : XCross T) (hxs : XStrip T)
    (hyc : YCross T) (hys : YStrip T) (hd : Desc0 T) (t : ℕ) (v0 : Fin (60 + 8 * t) × Fin (60 + 8 * t)) :
    ∃ p : (G T (60 + 8 * t)).Walk v0 v0, p.IsHamiltonianCycle := by
  have hconn := connected_G hP hQ hxc hxs hyc hys hd t
  have hcyc := isCycles_G hP hQ hdeg t
  have hne : ((G T (60 + 8 * t)).neighborSet v0).Nonempty := by
    rw [← Set.ncard_pos, Set.ncard_eq_toFinset_card', ← neighborFinset_def,
      card_neighborFinset_eq_degree, degree_G hP hQ hdeg]
    norm_num
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := (G T (60 + 8 * t)).connectedComponentMk v0) (v := v0) rfl hne
  refine ⟨p, ?_⟩
  refine ⟨hp, hp.isPath_tail.isHamiltonian_of_mem (fun a => ?_)⟩
  rw [Walk.support_tail_of_not_nil p hp.not_nil]
  have ha : a ∈ p.support := by
    rw [← Walk.mem_verts_toSubgraph, hverts, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact hconn.preconnected a v0
  rw [← p.cons_tail_support, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Walk.end_mem_tail_support hp.not_nil
  · exact ha

open Classical in
/-- The edges of a Hamiltonian cycle of the tour graph are all its edges. -/
lemma edges_eq (hdeg : Deg0 T) (t : ℕ) {v0 : Fin (60 + 8 * t) × Fin (60 + 8 * t)}
    (p : (G T (60 + 8 * t)).Walk v0 v0) (hp : p.IsHamiltonianCycle) (x y) :
    s(x, y) ∈ p.edges.toFinset ↔ (G T (60 + 8 * t)).Adj x y := by
  have hsub : p.edges.toFinset ⊆ (G T (60 + 8 * t)).edgeFinset := by
    intro e he
    rw [mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.1 he)
  have h1 : p.edges.toFinset.card = Fintype.card (Fin (60 + 8 * t) × Fin (60 + 8 * t)) := by
    rw [List.toFinset_card_of_nodup hp.isCycle.edges_nodup, Walk.length_edges, hp.length_eq]
  have h2 : (G T (60 + 8 * t)).edgeFinset.card =
      Fintype.card (Fin (60 + 8 * t) × Fin (60 + 8 * t)) := by
    have := sum_degrees_eq_twice_card_edges (G T (60 + 8 * t))
    simp only [degree_G hP hQ hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [heq, mem_edgeFinset, mem_edgeSet]

/-- No rail in the tour graph (literal source condition). -/
lemma norail_G (hrail : NoRail0 T) (t : ℕ) {v0 v1 v2 v3 : Fin (60 + 8 * t) × Fin (60 + 8 * t)}
    (h01 : (G T (60 + 8 * t)).Adj v0 v1) (h23 : (G T (60 + 8 * t)).Adj v2 v3)
    (k02 : (knightGraph (60 + 8 * t)).Adj v0 v2) (k13 : (knightGraph (60 + 8 * t)).Adj v1 v3) :
    (G T (60 + 8 * t)).Adj v0 v2 ∨ (G T (60 + 8 * t)).Adj v1 v3 := by
  obtain ⟨a, ha, ea⟩ := adjB_step h01
  obtain ⟨e, he, ee⟩ := adjB_step h23
  obtain ⟨b, hb, eb⟩ := knight_step k02
  obtain ⟨c, hc, ec⟩ := knight_step k13
  have hx : mvx a + mvx c = mvx b + mvx e := by
    have := congrArg Prod.fst ea; have := congrArg Prod.fst ee
    have := congrArg Prod.fst eb; have := congrArg Prod.fst ec
    simp only [step] at *; omega
  have hy : mvy a + mvy c = mvy b + mvy e := by
    have := congrArg Prod.snd ea; have := congrArg Prod.snd ee
    have := congrArg Prod.snd eb; have := congrArg Prod.snd ec
    simp only [step] at *; omega
  rcases para ha hb hc he hx hy with rfl | ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · left
    have : v2 = v1 := emb_inj (by rw [eb, ea])
    rw [this]; exact h01
  · have := norail_board hP hQ hrail (fam_n t) (fam_n t) (emb_onB v0) ha hb
      (by rw [← ea]; exact h01) (by rw [← eb, ← ee]; exact h23)
    rcases this with h | h
    · left; rw [G_adj_iff, eb]; exact h
    · right; rw [G_adj_iff, ec, ea]; exact h
  · right
    have : v3 = v0 := emb_inj (by
      rw [ec, ea]; simp only [step, h1, h2]; ext <;> simp)
    rw [this]; exact h01.symm

open Classical in
/-- Every board of the family carries a closed knight's tour without rails. -/
theorem tours_without_rails_of (hdeg : Deg0 T) (hrail : NoRail0 T) (hxc : XCross T)
    (hxs : XStrip T) (hyc : YCross T) (hys : YStrip T) (hd : Desc0 T) (t : ℕ) :
    ∃ (v : Fin (60 + 8 * t) × Fin (60 + 8 * t)) (q : (knightGraph (60 + 8 * t)).Walk v v),
      q.IsHamiltonianCycle ∧ rails q = ∅ := by
  have hpos : 0 < 60 + 8 * t := by omega
  let v0 : Fin (60 + 8 * t) × Fin (60 + 8 * t) := (⟨0, hpos⟩, ⟨0, hpos⟩)
  obtain ⟨p, hp⟩ := exists_ham_G hP hQ hdeg hxc hxs hyc hys hd t v0
  refine ⟨v0, p.mapLe (G_le (T := T) (60 + 8 * t)), ?_, ?_⟩
  · exact hp.map (by simp)
  · rw [rails, Finset.filter_eq_empty_iff]
    rintro r - ⟨w0, w1, w2, w3, -, h01, h23, k02, n02, k13, n13⟩
    rw [Walk.edges_mapLe_eq_edges] at h01 h23 n02 n13
    rw [edges_eq hP hQ hdeg t p hp] at h01 h23 n02 n13
    rcases norail_G hP hQ hrail t h01 h23 k02 k13 with h | h
    · exact n02 h
    · exact n13 h

end

end Rail
```

### `RailMain.lean`

```lean
import RailAssemble
import RailData
import RailRunMisc
import RailRunDeg
import RailRunRail
import RailRunDesc
import RailRunXcross
import RailRunXstrip
import RailRunYcross
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Rail Conjecture is false

For every `t`, the `(60 + 8t) × (60 + 8t)` board carries a closed knight's tour (a Hamiltonian
cycle of the knight's graph) with no rail at all. Hence no bound `rails ≥ c n` can hold for all
large `n`.
-/

namespace Rail

/-- Every board of side `60 + 8 t` has a closed knight's tour without rails. -/
theorem tours_without_rails (t : ℕ) :
    ∃ (v : Fin (60 + 8 * t) × Fin (60 + 8 * t)) (q : (knightGraph (60 + 8 * t)).Walk v v),
      q.IsHamiltonianCycle ∧ rails q = ∅ :=
  tours_without_rails_of (T := mkT rawT) (perX_of rawT perX_ok) (perY_of rawT perY_ok)
    (deg_of rawT deg_ok) (rail_of rawT rail_ok) (xcross_of rawT xcross_ok)
    (xstrip_of rawT xstrip_ok) (ycross_of rawT ycross_ok) (ystrip_of rawT rawP desc_ok)
    (desc0_of rawT rawP desc_ok) t

/-- **MathDB 345199.** Parberry's Rail Conjecture ("An `n × n` knight's tour has `Ω(n)` rails")
is false: for every `c > 0` and `N` there is `n ≥ N` and a closed knight's tour of the `n × n`
board with fewer than `c n` rails (in fact with none). -/
theorem rail_conjecture_false : ¬ RailConjecture := by
  rintro ⟨c, hc, N, hN⟩
  obtain ⟨v, q, hq, hr⟩ := tours_without_rails N
  have h := hN (60 + 8 * N) (by omega) v q hq
  rw [hr, Finset.card_empty] at h
  push_cast at h
  have : (0 : ℝ) < c * (60 + 8 * (N : ℝ)) := by positivity
  linarith

/-- The negation in explicit form. -/
theorem rail_conjecture_false' :
    ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ n ≥ N, ∃ (v : Fin n × Fin n) (q : (knightGraph n).Walk v v),
      q.IsHamiltonianCycle ∧ ((rails q).card : ℝ) < c * n := by
  intro c hc N
  obtain ⟨v, q, hq, hr⟩ := tours_without_rails N
  refine ⟨60 + 8 * N, by omega, v, q, hq, ?_⟩
  rw [hr, Finset.card_empty]
  push_cast
  positivity

end Rail

#print axioms Rail.rail_conjecture_false
#print axioms Rail.rail_conjecture_false'
#print axioms Rail.tours_without_rails
```


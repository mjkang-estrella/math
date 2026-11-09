import Definitions
import Lean.Elab.Tactic.Omega
namespace EBC337062
open SimpleGraph Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

/-- Labels increasing by at most one on edges give lower bounds for walks. -/
theorem label_le_walk (d : V → ℕ)
    (step : ∀ a b, G.Adj a b → d a ≤ d b + 1)
    {a b : V} (w : G.Walk a b) : d a ≤ w.length + d b := by
  induction w with
  | nil => simp
  | @cons a b c h w ih =>
    have := step a b h
    simp only [Walk.length_cons]
    omega

/-- A zero label only at the target, together with predecessors, constructs walks. -/
theorem exists_walk_of_labels (t : V) (d : V → ℕ)
    (zero : ∀ a, d a = 0 ↔ a = t)
    (pred : ∀ a, a ≠ t → ∃ b, G.Adj a b ∧ d b + 1 = d a)
    (a : V) : ∃ w : G.Walk a t, w.length = d a := by
  have aux : ∀ n a, d a = n → ∃ w : G.Walk a t, w.length = d a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hat : a = t
      · subst a
        exact ⟨.nil, by simp [(zero t).2 rfl]⟩
      · obtain ⟨b, hab, hb⟩ := pred a hat
        obtain ⟨w, hw⟩ := ih (d b) (by omega) b rfl
        exact ⟨.cons hab w, by simp [hw, hb]⟩
  exact aux (d a) a rfl

theorem dist_eq_labels (t : V) (d : V → ℕ)
    (zero : ∀ a, d a = 0 ↔ a = t)
    (step : ∀ a b, G.Adj a b → d a ≤ d b + 1)
    (pred : ∀ a, a ≠ t → ∃ b, G.Adj a b ∧ d b + 1 = d a)
    (a : V) : G.dist a t = d a := by
  obtain ⟨w, hw⟩ := exists_walk_of_labels G t d zero pred a
  obtain ⟨p, hp⟩ := w.reachable.exists_walk_length_eq_dist
  apply Nat.le_antisymm
  · simpa [hw] using G.dist_le w
  · have h := label_le_walk G d step p
    simpa [hp, (zero t).2 rfl] using h

/-- Count all fixed-length walks by their first edge, without enumeration. -/
theorem walk_count_succ (n : ℕ) (a t : V) :
    (G.finsetWalkLength (n+1) a t).card =
      ∑ b : G.neighborSet a, (G.finsetWalkLength n b t).card := by
  classical
  rw [SimpleGraph.finsetWalkLength, Finset.card_biUnion]
  · simp
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro w hb hc
    obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hb
    obtain ⟨q, _, hq⟩ := Finset.mem_map.mp hc
    have h : b.val = c.val := by
      have hs := congrArg SimpleGraph.Walk.snd (hp.trans hq.symm)
      change (Walk.cons b.property p).snd = (Walk.cons c.property q).snd at hs
      rwa [Walk.snd_cons, Walk.snd_cons] at hs
    exact hbc (Subtype.ext h)

theorem sigma_self (a : V) : sigma G a a = 1 := by
  rw [sigma_eq_walk_count, SimpleGraph.dist_self]
  simp [SimpleGraph.finsetWalkLength]

/-- No walk can reach a vertex at a length below its certified label. -/
theorem walk_count_zero_of_lt (t : V) (d : V → ℕ) (dt : d t = 0)
    (step : ∀ a b, G.Adj a b → d a ≤ d b + 1)
    (a : V) (n : ℕ) (hn : n < d a) : (G.finsetWalkLength n a t).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have h := label_le_walk G d step w
  have hl := G.mem_finsetWalkLength_iff.mp hw
  omega

/-- Local BFS equations determine the literal shortest-path counts. -/
theorem sigma_eq_of_bfs (t : V) (d c : V → ℕ)
    (zero : ∀ a, d a = 0 ↔ a = t)
    (step : ∀ a b, G.Adj a b → d a ≤ d b + 1)
    (pred : ∀ a, a ≠ t → ∃ b, G.Adj a b ∧ d b + 1 = d a)
    (ct : c t = 1)
    (rec : ∀ a, a ≠ t → c a =
      ∑ b : G.neighborSet a, if d b + 1 = d a then c b else 0)
    (a : V) : sigma G a t = c a := by
  classical
  have dist := dist_eq_labels G t d zero step pred
  have aux : ∀ n a, d a = n → sigma G a t = c a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hat : a = t
      · subst a
        rw [sigma_self, ct]
      · have hn : 0 < n := by
          have : d a ≠ 0 := fun hz => hat ((zero a).1 hz)
          omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        rw [sigma_eq_walk_count, dist a, ha, hk, walk_count_succ, rec a hat]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : d b + 1 = d a
        · rw [ite_eq_left hb]
          have hdb : d b = k := by omega
          have hi := ih (d b) (by omega) b rfl
          rw [sigma_eq_walk_count, dist b, hdb] at hi
          exact hi
        · rw [ite_eq_right hb]
          apply walk_count_zero_of_lt G t d ((zero t).2 rfl) step
          have hs := step a b b.property
          omega
  exact aux (d a) a rfl
end EBC337062

import Definitions

namespace Schrijver

-- Decode before testing: the bit convention is explicit and finite.
def decode (n m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => m.testBit i.val)

def validMask (n k m : ℕ) : Bool :=
  decide (m < 2^n) && decide ((decode n m).card = k) &&
    (List.finRange n).all (fun i =>
      !(m.testBit i.val && m.testBit ((i.val+1)%n)))

theorem validMask_sound {n k m : ℕ} (h : validMask n k m = true) :
    m < 2^n ∧ (decode n m).card = k ∧ Stable n (decode n m) := by
  simp only [validMask, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro i hi j hj heq
  have hi' : m.testBit i.val = true := by simpa [decode] using hi
  have hj' : m.testBit j.val = true := by simpa [decode] using hj
  have hh := h.2 i (by simp)
  rw [← heq, hi', hj'] at hh
  cases hh

-- A finite Bool test, with an explicit completeness premise for its index list.
def labelCheck {α : Type*} (vs : List α) (edge : α → α → Bool) (d : α → ℕ) : Bool :=
  vs.all (fun u => vs.all (fun v => !edge u v || decide (d v ≤ d u + 1)))

theorem labelCheck_sound {α : Type*} (vs : List α) (edge : α → α → Bool)
    (d : α → ℕ) (h : labelCheck vs edge d = true)
    {u v : α} (hu : u ∈ vs) (hv : v ∈ vs) (he : edge u v = true) :
    d v ≤ d u + 1 := by
  simp only [labelCheck, List.all_eq_true] at h
  have hh := h u hu v hv
  simpa [he] using hh

-- Induction on walks is the metric soundness step for lower certificates.
theorem label_walk_bound {α : Type*} {G : SimpleGraph α} (d : α → ℕ)
    (hedge : ∀ u v, G.Adj u v → d v ≤ d u + 1)
    {a b : α} (p : G.Walk a b) : d b ≤ d a + p.length := by
  induction p with
  | nil => simp
  | @cons a v b hav p ih =>
    have ha := hedge a v hav
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem labels_lower_distance {α : Type*} {G : SimpleGraph α} (d : α → ℕ)
    (hedge : ∀ u v, G.Adj u v → d v ≤ d u + 1)
    {a b : α} (ha : d a = 0) (hr : G.Reachable a b) : d b ≤ G.dist a b := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hb := label_walk_bound d hedge p
  simpa [ha, hp] using hb

-- Parent labels decrease strictly. This is sufficient; a DFS/BFS algorithm is unnecessary.
theorem parent_walk {α : Type*} {G : SimpleGraph α} (root : α)
    (parent : α → α) (depth : α → ℕ)
    (hzero : ∀ v, depth v = 0 → v = root)
    (hstep : ∀ v, depth v ≠ 0 → G.Adj v (parent v) ∧ depth (parent v) + 1 = depth v) :
    ∀ v, ∃ p : G.Walk v root, p.length = depth v := by
  intro v
  have main : ∀ t, ∀ v, depth v = t → ∃ p : G.Walk v root, p.length = depth v := by
    intro t
    induction t with
    | zero =>
      intro v hv
      have he := hzero v hv
      subst v
      exact ⟨.nil, by simp [hv]⟩
    | succ t ih =>
      intro v hv
      have hn : depth v ≠ 0 := by omega
      obtain ⟨he, hd⟩ := hstep v hn
      obtain ⟨p, hp⟩ := ih (parent v) (by omega)
      exact ⟨.cons he p, by simp only [SimpleGraph.Walk.length_cons]; omega⟩
  exact main (depth v) v rfl

theorem parent_connected {α : Type*} {G : SimpleGraph α} (root : α)
    (parent : α → α) (depth : α → ℕ)
    (hzero : ∀ v, depth v = 0 → v = root)
    (hstep : ∀ v, depth v ≠ 0 → G.Adj v (parent v) ∧ depth (parent v) + 1 = depth v) :
    G.Connected := by
  let : Nonempty α := ⟨root⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p, _⟩ := parent_walk root parent depth hzero hstep u
  obtain ⟨q, _⟩ := parent_walk root parent depth hzero hstep v
  exact ⟨p.append q.reverse⟩

def parentCheck {α : Type*} [DecidableEq α] (vs : List α)
    (edge : α → α → Bool) (root : α) (parent : α → α) (depth : α → ℕ) : Bool :=
  vs.all (fun v => if depth v = 0 then decide (v = root)
    else edge v (parent v) && decide (depth (parent v) + 1 = depth v))

theorem parentCheck_sound {α : Type*} [DecidableEq α] (vs : List α)
    (edge : α → α → Bool) (root : α) (parent : α → α) (depth : α → ℕ)
    (h : parentCheck vs edge root parent depth = true) (v : α) (hv : v ∈ vs) :
    (depth v = 0 → v = root) ∧
    (depth v ≠ 0 → edge v (parent v) = true ∧ depth (parent v) + 1 = depth v) := by
  have hh := (List.all_eq_true.mp h) v hv
  change (if depth v = 0 then decide (v = root)
    else edge v (parent v) && decide (depth (parent v) + 1 = depth v)) = true at hh
  by_cases hz : depth v = 0
  · simp [hz] at hh
    exact ⟨fun _ => hh, fun hn => (hn hz).elim⟩
  · simp [hz] at hh
    exact ⟨fun he => (hz he).elim, fun _ => hh⟩

end Schrijver

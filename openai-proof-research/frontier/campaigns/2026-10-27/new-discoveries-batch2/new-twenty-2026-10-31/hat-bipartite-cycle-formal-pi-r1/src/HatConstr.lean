import HatCycle

/-!
# Canonical pairs of hat-graph vertices

Toolbox for the literal label model: unordered pairs of labels `0..2s-1` in
canonical increasing orientation, with the unordered-equality lemma.
-/

/-- Canonical (increasing-label) pair of two vertices. -/
def hatCan (s : Nat) (u v : Fin (2 * s)) : Fin (2 * s) × Fin (2 * s) :=
  (⟨min u.val v.val, by omega⟩, ⟨max u.val v.val, by omega⟩)

theorem hatCan_swap (s : Nat) (u v : Fin (2 * s)) : hatCan s u v = hatCan s v u := by
  unfold hatCan
  simp [Nat.min_comm, Nat.max_comm]

/-- Fin equality from equality of labels. -/
theorem hatFinEq {s : Nat} {x y : Fin (2 * s)} (h : x.val = y.val) : x = y :=
  Fin.val_injective h

/-- Unordered-pair equality of canonical pairs. -/
theorem hatCan_inj {s : Nat} {a b c d : Fin (2 * s)} :
    hatCan s a b = hatCan s c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold hatCan
  constructor
  · intro h
    have h1 : min a.val b.val = min c.val d.val := by
      have := congrArg (fun p : Fin (2 * s) × Fin (2 * s) => p.1.val) h
      simpa using this
    have h2 : max a.val b.val = max c.val d.val := by
      have := congrArg (fun p : Fin (2 * s) × Fin (2 * s) => p.2.val) h
      simpa using this
    rcases Nat.lt_trichotomy a.val b.val with hab | heq | hba
    · have hcd : c.val = a.val ∧ d.val = b.val ∨ d.val = a.val ∧ c.val = b.val := by omega
      rcases hcd with hc | hc
      · exact Or.inl ⟨hatFinEq hc.1.symm, hatFinEq hc.2.symm⟩
      · exact Or.inr ⟨hatFinEq hc.1.symm, hatFinEq hc.2.symm⟩
    · have hcdeq : c.val = a.val ∧ d.val = a.val := by omega
      refine Or.inl ⟨hatFinEq hcdeq.1.symm, ?_⟩
      have hba : b = a := hatFinEq heq.symm
      rw [hba]
      exact hatFinEq hcdeq.2.symm
    · have hcd : c.val = b.val ∧ d.val = a.val ∨ d.val = b.val ∧ c.val = a.val := by omega
      rcases hcd with hc | hc
      · exact Or.inr ⟨hatFinEq hc.2.symm, hatFinEq hc.1.symm⟩
      · exact Or.inl ⟨hatFinEq hc.2.symm, hatFinEq hc.1.symm⟩
  · rintro (⟨hac, hbd⟩ | ⟨had, hbc⟩)
    · subst hac; subst hbd; rfl
    · subst had; subst hbc
      exact hatCan_swap s a b

/-- The canonical pair of an A-vertex and a B-vertex is a genuine hat edge:
odd+positive-even labels, distinct, so the A-B disjunct of the edge
predicate holds after canonicalization. -/
theorem hatCan_mem_AB (s : Nat) (u v : Fin (2 * s)) (hu : u.val % 2 = 1)
    (hv : v.val % 2 = 0) (hv0 : v.val ≠ 0) : hatCan s u v ∈ hatEdgeSet s := by
  unfold hatEdgeSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hne : u.val ≠ v.val := by
    intro h; rw [h] at hu; omega
  rw [show (hatCan s u v).1.val = min u.val v.val from rfl,
      show (hatCan s u v).2.val = max u.val v.val from rfl]
  rcases Nat.lt_or_ge u.val v.val with hlt | hge
  · refine ⟨by omega, ?_⟩
    refine Or.inl ⟨?_, ?_, ?_⟩ <;> omega
  · refine ⟨by omega, ?_⟩
    refine Or.inl ⟨?_, ?_, ?_⟩ <;> omega

/-- Swapped orientation of `hatCan_mem_AB`. -/
theorem hatCan_mem_BA (s : Nat) (u v : Fin (2 * s)) (hu : u.val % 2 = 1)
    (hv : v.val % 2 = 0) (hv0 : v.val ≠ 0) : hatCan s v u ∈ hatEdgeSet s := by
  rw [hatCan_swap]
  exact hatCan_mem_AB s u v hu hv hv0

/-- The A-B tour edge `x j -- t j` as a genuine hat edge. -/
def tourAB (s : Nat) (x : Fin s → Fin (2 * s)) (t : Fin (s - 1) → Fin (2 * s))
    (hx : ∀ i, (x i).val % 2 = 1) (ht : ∀ j, (t j).val % 2 = 0)
    (ht0 : ∀ j, (t j).val ≠ 0) (j : Fin (s - 1)) : HEdge s :=
  ⟨hatCan s (x (Fin.castLE (by omega) j)) (t j),
    hatCan_mem_AB s (x (Fin.castLE (by omega) j)) (t j) (hx (Fin.castLE (by omega) j)) (ht j) (ht0 j)⟩

/-- The successor A-index of `j : Fin (s-1)` inside `Fin s`. -/
def tourSucc (s : Nat) (j : Fin (s - 1)) : Fin s := ⟨j.val + 1, by omega⟩

/-- The B-A tour edge `t j -- x (j+1)` as a genuine hat edge. -/
def tourBA (s : Nat) (x : Fin s → Fin (2 * s)) (t : Fin (s - 1) → Fin (2 * s))
    (hx : ∀ i, (x i).val % 2 = 1) (ht : ∀ j, (t j).val % 2 = 0)
    (ht0 : ∀ j, (t j).val ≠ 0) (j : Fin (s - 1)) : HEdge s :=
  ⟨hatCan s (t j) (x (tourSucc s j)), hatCan_mem_BA s (x (tourSucc s j)) (t j) (hx (tourSucc s j)) (ht j) (ht0 j)⟩

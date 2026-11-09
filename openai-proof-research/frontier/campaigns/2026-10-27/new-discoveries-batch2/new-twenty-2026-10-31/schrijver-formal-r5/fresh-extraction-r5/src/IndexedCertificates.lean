import Rotations
namespace Schrijver

def packedGet (width data i : ℕ) : ℕ := (data / 2^(width*i)) % 2^width

def indexedEdge (masks : ℕ → ℕ) {N : ℕ} (u v : Fin N) : Bool :=
  decide (u ≠ v) && decide ((masks u.val &&& masks v.val) = 0)

noncomputable def indexedGraph (N : ℕ) (masks : ℕ → ℕ) : SimpleGraph (Fin N) where
  Adj u v := u ≠ v ∧ (masks u.val &&& masks v.val) = 0
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by rw [Nat.and_comm]; exact h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

theorem indexedEdge_iff (masks : ℕ → ℕ) {N : ℕ} (u v : Fin N) :
    indexedEdge masks u v = true ↔ (indexedGraph N masks).Adj u v := by
  simp [indexedEdge, indexedGraph]

def indexDepth {N : ℕ} (ds : ℕ → ℕ) (v : Fin N) : ℕ := ds v.val

def indexParent {N : ℕ} [NeZero N] (ps : ℕ → ℕ) (v : Fin N) : Fin N :=
  Fin.ofNat N (ps v.val)

def treeCheck (N : ℕ) [NeZero N] (masks ps ds : ℕ → ℕ) (root : Fin N) (bound : ℕ) : Bool :=
  parentCheck (List.finRange N) (indexedEdge masks) root (indexParent ps) (indexDepth ds) &&
    (List.finRange N).all (fun v => decide (indexDepth ds v ≤ bound))

theorem treeCheck_sound (N : ℕ) [NeZero N] (masks ps ds : ℕ → ℕ) (root : Fin N)
    (bound : ℕ) (h : treeCheck N masks ps ds root bound = true) :
    (indexedGraph N masks).Connected ∧ ∀ v, ∃ p : (indexedGraph N masks).Walk v root,
      p.length ≤ bound := by
  simp only [treeCheck, Bool.and_eq_true] at h
  obtain ⟨hc, hd⟩ := h
  have hh (v : Fin N) := parentCheck_sound (List.finRange N) (indexedEdge masks) root
    (indexParent ps) (indexDepth ds) hc v (by simp)
  have hz : ∀ v, indexDepth ds v = 0 → v = root := fun v => (hh v).1
  have hs : ∀ v, indexDepth ds v ≠ 0 →
      (indexedGraph N masks).Adj v (indexParent ps v) ∧
        indexDepth ds (indexParent ps v) + 1 = indexDepth ds v := by
    intro v hv
    exact ⟨(indexedEdge_iff _ _ _).mp ((hh v).2 hv).1, ((hh v).2 hv).2⟩
  refine ⟨parent_connected root (indexParent ps) (indexDepth ds) hz hs, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := parent_walk root (indexParent ps) (indexDepth ds) hz hs v
  refine ⟨p, hp.trans_le ?_⟩
  exact of_decide_eq_true ((List.all_eq_true.mp hd) v (by simp))

theorem indexedLabel_sound (N : ℕ) (masks ds : ℕ → ℕ)
    (h : labelCheck (List.finRange N) (indexedEdge masks) (indexDepth ds) = true) :
    ∀ u v, (indexedGraph N masks).Adj u v → indexDepth ds v ≤ indexDepth ds u + 1 := by
  intro u v huv
  exact labelCheck_sound _ _ _ h (by simp) (by simp) ((indexedEdge_iff _ _ _).mpr huv)

end Schrijver

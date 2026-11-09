import Mathlib.Combinatorics.SimpleGraph.Diam
import Lean.Elab.Tactic.Omega

namespace Schrijver

def Stable (n : ℕ) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (j.val ≠ (i.val + 1) % n)

abbrev Vertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k ∧ Stable n s}

noncomputable def SG (n k : ℕ) : SimpleGraph (Vertex n k) where
  Adj a b := a ≠ b ∧ Disjoint a.val b.val
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def diam {α : Type*} (G : SimpleGraph α) : ℕ := G.diam

def SchrijverUnitGap : Prop := ∀ k r : ℕ, 2 ≤ r → r + 2 ≤ k →
  ((diam (SG (2*k+r) k) : ℤ) - diam (SG (2*k+r+1) k)) ∈ ({0, 1} : Set ℤ)

-- These are residual obligations, not assumptions installed in the environment.
def LowerCertificateBridge : Prop :=
  (SG 27 12).Connected ∧ ∃ a b, 8 ≤ (SG 27 12).dist a b

def UpperCertificateBridge : Prop :=
  (SG 28 12).Connected ∧ ∀ a b, ∃ p : (SG 28 12).Walk a b, p.length ≤ 6

 theorem lower_diameter (h : LowerCertificateBridge) : 8 ≤ diam (SG 27 12) := by
  classical
  obtain ⟨hc, a, b, hab⟩ := h
  let : Nonempty (Vertex 27 12) := ⟨a⟩
  have ht := (SimpleGraph.connected_iff_ediam_ne_top (G := SG 27 12)).mp hc
  exact hab.trans (SimpleGraph.dist_le_diam ht)

 theorem upper_diameter (h : UpperCertificateBridge) : diam (SG 28 12) ≤ 6 := by
  classical
  let : Nonempty (Vertex 28 12) := h.1.nonempty
  obtain ⟨a, b, hab⟩ := (SG 28 12).exists_dist_eq_diam
  obtain ⟨p, hp⟩ := h.2 a b
  change (SG 28 12).diam ≤ 6
  rw [← hab]
  exact (SimpleGraph.dist_le p).trans hp

-- Conditional endpoint only: neither residual proposition is claimed proved.
theorem mathdb_352827_conditional
    (lower : LowerCertificateBridge) (upper : UpperCertificateBridge) : ¬ SchrijverUnitGap := by
  intro h
  have hg := h 12 3 (by decide) (by decide)
  change ((diam (SG 27 12) : ℤ) - diam (SG 28 12)) ∈ ({0, 1} : Set ℤ) at hg
  have hl := lower_diameter lower
  have hu := upper_diameter upper
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg <;> omega

end Schrijver

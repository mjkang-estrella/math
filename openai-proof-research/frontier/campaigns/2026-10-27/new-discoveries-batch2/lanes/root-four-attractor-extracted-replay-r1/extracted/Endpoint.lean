import Attractor
set_option autoImplicit false
set_option warningAsError true
namespace FourAttractor
theorem no_four (g : Finset (Fin w.length)) (hg : Attractor w g) : ¬ g.card ≤ 4 := by
  intro hc
  have hw : w.length = 36 := by decide
  let _ : Inhabited (Fin w.length) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a,b,c,d,habcd⟩ := coverFour g.toList (by simpa using hc)
  have cover : ∀ p ∈ g, p = a ∨ p = b ∨ p = c ∨ p = d := by simpa using habcd
  have one (l r : Nat) (h : ∃ p ∈ g, inI p.val l r) : hit a.val b.val c.val d.val l r := by
    obtain ⟨p,hp,h⟩ := h
    rcases cover p hp with he|he|he|he <;> subst p <;> simp_all [hit]
  have two (l r s t : Nat) (h : ∃ p ∈ g, inI p.val l r ∨ inI p.val s t) :
      hitTwo a.val b.val c.val d.val l r s t := by
    obtain ⟨p,hp,h⟩ := h
    rcases h with h|h
    · exact Or.inl (one l r ⟨p,hp,h⟩)
    · exact Or.inr (one s t ⟨p,hp,h⟩)
  exact obstruction a.val b.val c.val d.val
    (one _ _ (necessary1 g hg)) (one _ _ (necessary2 g hg)) (one _ _ (necessary3 g hg))
    (one _ _ (necessary4 g hg)) (one _ _ (necessary5 g hg)) (one _ _ (necessary6 g hg))
    (one _ _ (necessary7 g hg)) (one _ _ (necessary8 g hg)) (one _ _ (necessary9 g hg))
    (two _ _ _ _ (necessary10 g hg)) (two _ _ _ _ (necessary11 g hg))
def SourceClaim : Prop := ∀ d t : Nat → Bool, ∀ n : Nat,
  ∃ g : Finset (Fin (prefixWord d t n).length), Attractor (prefixWord d t n) g ∧ g.card ≤ 4
theorem source_refuted : ¬ SourceClaim := by
  intro h
  have h5 := h delta anti 5
  rw [fifth] at h5
  obtain ⟨g,hg,hc⟩ := h5
  exact no_four g hg hc
theorem intrinsic_witness :
    prefixWord delta anti 5 = w ∧ theta false w = w ∧
    (∀ i (hi : i < w.length), w[i] = infiniteWord delta anti i) ∧
    (∀ g : Finset (Fin w.length), Attractor w g → 4 < g.card) := by
  refine ⟨fifth, by decide, ?_, ?_⟩
  · intro i hi
    have hp := prefixes_infinite delta anti 5 i
    simp only [fifth] at hp
    exact hp hi
  · intro g hg
    have := no_four g hg
    omega
end FourAttractor

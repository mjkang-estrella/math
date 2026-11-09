from pathlib import Path
s=Path('Draft.txt').read_text(); s=s[s.index('import Mathlib'):s.index('/-\nNotes for')]; s=s.replace('IRGraphPath','IR350452')
a=s.index('/-- An `IR(G)`-set'); b=s.index('/-- The swap relation',a)
s=s[:a]+'''noncomputable def IR (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (Irredundant G)).sup Finset.card

lemma ir_upper {G : SimpleGraph V} {D : Finset V} (h : Irredundant G D) :
    D.card ≤ IR G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ D, h⟩)

lemma ir_attained (G : SimpleGraph V) : ∃ D, Irredundant G D ∧ D.card = IR G := by
  classical
  have hempty : Irredundant G ∅ := by simp [Irredundant]
  have hn : (Finset.univ.filter (Irredundant G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hempty⟩⟩
  obtain ⟨D, hD, heq⟩ := Finset.exists_mem_eq_sup hn Finset.card
  exact ⟨D, (Finset.mem_filter.mp hD).2, heq.symm⟩

def IRSet (G : SimpleGraph V) (D : Finset V) : Prop :=
  Irredundant G D ∧ D.card = IR G

abbrev IsIRSet := @IRSet

lemma irSet_iff_max (G : SimpleGraph V) (D : Finset V) :
    IRSet G D ↔ Irredundant G D ∧ ∀ E, Irredundant G E → E.card ≤ D.card := by
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨h, fun E he => hc ▸ ir_upper he⟩
  · rintro ⟨h, hm⟩
    obtain ⟨E, he, hc⟩ := ir_attained G
    exact ⟨h, le_antisymm (ir_upper h) (hc ▸ hm E he)⟩

''' +s[b:]
s=s.replace('le_antisymm (hB.2 A hA.1) (hA.2 B hB.1)','hA.2.trans hB.2.symm')
s=s.replace('Nonempty (IRGraph G ≃g H)','Nonempty (H ≃g IRGraph G)')
s=s.replace('Finset.not_mem_erase','Finset.notMem_erase')
s=s.replace('  constructor\n  · rintro ⟨hirr, hmax⟩','  rw [irSet_iff_max]\n  constructor\n  · rintro ⟨hirr, hmax⟩')
s=s.replace('⟨pathIso.symm⟩','⟨pathIso⟩')
a=s.index('/-- MathDB 350452');s=s[:a]+'''def Conjecture : Prop :=
  (∀ n : ℕ, 3 ≤ n → ¬ IsIRGraph (SimpleGraph.pathGraph n)) ∧
  (∀ n : ℕ, 5 ≤ n → ¬ IsIRGraph (SimpleGraph.cycleGraph n))

theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨hP, -⟩
  exact hP 9 (by norm_num) pathGraph_nine_isIRGraph

end IR350452
'''
a=s.index('/-! ### The 9-vertex');Path('General.lean').write_text(s[:a]+'\nend IR350452\n')
b=s.index('/-- Every irredundant');Path('Finite.lean').write_text('import General\nopen Finset\nnamespace IR350452\n'+s[a:b]+'\nend IR350452\n')
Path('Endpoint.lean').write_text('import Finite\nopen Finset\nnamespace IR350452\n'+s[b:])

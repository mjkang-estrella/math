from pathlib import Path
p=Path('Definitions.lean');s=p.read_text().replace('import Mathlib.Data.Finset.Card','import Mathlib.Data.Finset.Card\nimport Mathlib.Order.Interval.Finset.Nat').replace('s <+ w','s.Sublist w').replace('universe','wordUniverse').replace('simp [isoB, Iso, List.all_eq_true]','simp only [isoB, Iso, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]').replace('| zero => simp [allWords]','| zero => cases w <;> simp [allWords]').replace('(ih u).mp hu','(ih xs).mp hu').replace('def SourceCount','noncomputable def SourceCount')
p.write_text(s)

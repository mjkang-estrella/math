from pathlib import Path
p=Path('formal/Tail.lean');s=p.read_text()
start=s.index('noncomputable def tail')
end=s.index('theorem tail_tendsto')
base=s[:start].replace('import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral\n','').replace('import Mathlib.MeasureTheory.Integral.Bochner.Basic\n','').replace('import Mathlib.MeasureTheory.Integral.DominatedConvergence\n','').replace('open Real Filter MeasureTheory Set','open Real Filter Set')+'end Renyi\n'
Path('formal/Pointwise.lean').write_text(base)
Path('formal/Majorant.lean').write_text('import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Ring\nset_option autoImplicit false\nset_option warningAsError true\nopen Real MeasureTheory Set\nnamespace Renyi\n'+s[s.index('theorem majorant_integrable'):end]+'end Renyi\n')
p.write_text('import Pointwise\nimport Majorant\nimport Mathlib.MeasureTheory.Integral.DominatedConvergence\nset_option autoImplicit false\nset_option warningAsError true\nopen Real Filter MeasureTheory Set\nopen scoped Topology\nnamespace Renyi\n'+s[start:s.index('theorem majorant_integrable')]+s[end:])

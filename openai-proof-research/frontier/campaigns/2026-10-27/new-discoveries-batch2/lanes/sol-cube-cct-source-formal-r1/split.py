from pathlib import Path
L=Path(__file__).parent
s=(L/'Cube.lean').read_text()
a=s.index('theorem point_injective');b=s.index('theorem score_preserved')
defs=s[s.index('namespace Cube'):a].replace('def point (v : V) : Fin 5 → ℝ := fun i => (zcoord v i : ℝ)\n','')
(L/'Finite.lean').write_text('import Mathlib.Data.Fintype.Prod\nimport Mathlib.Data.Finset.Card\nimport Mathlib.Algebra.BigOperators.Group.Finset.Basic\nimport Mathlib.Data.Int.Basic\nset_option autoImplicit false\nset_option warningAsError true\n'+defs+s[b:])
imports=s[:s.index('namespace Cube')]
(L/'Cube.lean').write_text('import Finite\n'+imports+'namespace Cube\ndef point (v : V) : Fin 5 → ℝ := fun i => (zcoord v i : ℝ)\n'+s[a:b]+'end Cube\n')

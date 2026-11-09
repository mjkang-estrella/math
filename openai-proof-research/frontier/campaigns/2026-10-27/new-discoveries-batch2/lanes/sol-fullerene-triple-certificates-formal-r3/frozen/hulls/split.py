from pathlib import Path
L=Path(__file__).resolve().parent
s=(L/'Geometry.lean').read_text();(L/'Geometry-unsplit.lean.txt').write_text(s)
start=s.index('def normalMap');mid=s.index('theorem hull_of_complete_vertices')
prefix='set_option autoImplicit false\nset_option warningAsError true\nnoncomputable section\nnamespace FullereneGeometry\n'
(L/'Rank.lean').write_text('import Literal\nimport Mathlib.LinearAlgebra.Dual.Lemmas\n'+prefix+s[start:mid]+'end FullereneGeometry\n')
(L/'Hulls.lean').write_text('import Literal\nimport Mathlib.Analysis.Convex.KreinMilman\nimport Mathlib.Analysis.Convex.Topology\n'+prefix+s[mid:])
(L/'Geometry.lean').write_text('import Rank\nimport Hulls\n')

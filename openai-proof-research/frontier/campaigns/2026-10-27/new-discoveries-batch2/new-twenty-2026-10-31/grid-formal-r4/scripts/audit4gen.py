from pathlib import Path
p=Path(__file__).resolve().parent.parent
s=(p/'src/Audit3.lean').read_text()
mods=['GridDegrees','GridSideRigidity','GridFreeClassification','GridOrbitPaths','GridTransposeGroup','GridOrbitSmall','GridFinal4']
s=s.replace('open Lean Elab Command\n',''.join('import all '+m+'\n' for m in mods)+'open Lean Elab Command\n',1)
s=s.replace('`GridFreePaths, `GridFinal3]','`GridFreePaths, `GridFinal3, '+', '.join('`'+m for m in mods)+']')
s=s.replace('#print axioms Grid343536.exceptional_no_iso','#print axioms Grid343536.exceptional_no_iso\n#print axioms Grid343536.main_orbit_two\n#print axioms Grid343536.main_orbit_three')
s=s.replace('insert `GridFinal3','insert `GridFinal4').replace('#print axioms GridFinal3.mathdb_343536','#print axioms GridFinal4.mathdb_343536\n#print axioms Grid343536.free_classification\n#print axioms Grid343536.main_orbit_column_path\n#print axioms Grid343536.main_orbit_row_path')
(p/'src/Audit4.lean').write_text(s)

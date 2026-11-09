from pathlib import Path
import hashlib,zipfile
p=Path(__file__).resolve().parent.parent
z=p.parent/'grid-formal-r4/grid-formal-r4-source.zip'
assert hashlib.sha256(z.read_bytes()).hexdigest()=='384a9c6a9a4e28e0e922f6545c1516216578fb8f4c73d5e469d157fddc2e378d'
with zipfile.ZipFile(z) as f:
 for n in f.namelist():
  assert not n.startswith('/') and '..' not in Path(n).parts
  if n.startswith('src/') and n.endswith('.lean'):
   assert f.read(n)==(p/n).read_bytes(),n
assert len((p/'frozen-before.sha256').read_text().splitlines())==31
s=(p/'src/Audit4.lean').read_text()
mods=['GridLadderLayers','GridLadderOrbit','GridOrdinaryLayers','GridBorderWalk','GridSideColors','GridFinal5']
s=s.replace('open Lean Elab Command\n',''.join('import all '+m+'\n' for m in mods)+'open Lean Elab Command\n',1)
s=s.replace('`GridFinal4]','`GridFinal4, '+', '.join('`'+m for m in mods)+']')
s=s.replace('insert `GridFinal4','insert `GridFinal5')
s=s.replace('#print axioms GridFinal4.mathdb_343536','#print axioms GridFinal5.mathdb_343536\n#print axioms Grid343536.main_orbit_ladder\n#print axioms Grid343536.main_orbit_transposed_ladder\n#print axioms Grid343536.main_orbit_of_ordinary_border')
(p/'src/Audit5.lean').write_text(s)
print('Frozen zip and all 31 source modules match. Audit5 generated.')

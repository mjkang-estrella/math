import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
imports=''
for i in range(2):
 for x in range(8):
  module=f'C{i}R{x}';imports+=f'import {module}\n'
  s='import Base\nnamespace Rainbow\nset_option synthInstance.maxSize 1000\nset_option maxRecDepth 3000\nset_option maxHeartbeats 3000000\n'
  for y in range(8):
   if x==y:continue
   g='G' if i==0 else 'Gᶜ'
   s+=f'theorem cert{i}_{x}_{y} : CutCert {g} color{i} {x} {y} (cut{i} {x} {y}) (side{i} {x} {y}) := by\n  dsimp [CutCert, RainbowOn, cut{i}, side{i}, color{i}]\n  decide\n'
  s+='end Rainbow\n'
  (D/f'{module}.lean').write_text(s)
old=(D/'Certificates.lean').read_text()
tail=old[old.index('theorem cert0 :'):]
(D/'Certificates.lean').write_text(imports+'namespace Rainbow\n'+tail)

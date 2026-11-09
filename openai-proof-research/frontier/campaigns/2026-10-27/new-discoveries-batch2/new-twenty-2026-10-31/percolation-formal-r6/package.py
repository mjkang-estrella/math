import pathlib,re,hashlib,json,shutil
r=pathlib.Path(__file__).resolve().parent
s=r/'inherited/src'; dest=r/'packet/src'; order=(r/'inherited/module-order.txt').read_text().splitlines()
need=set()
def visit(n):
 if n in need:return
 need.add(n)
 for m in re.findall(r'^import (\w+)',(s/f'{n}.lean').read_text(),re.M):
  if (s/f'{m}.lean').exists():visit(m)
for n in ['Normalize','NormalizedExport','Control4','Control5','Structure','Closure','FiniteSystem','InputLink','Endpoint']:visit(n)
mods=[n for n in order if n in need]
rows=[]
for n in mods:
 data=(s/f'{n}.lean').read_bytes(); (dest/f'{n}.lean').write_bytes(data)
 assert data==(dest/f'{n}.lean').read_bytes()
 rows.append({'module':n,'sha256':hashlib.sha256(data).hexdigest()})
(r/'retained-source-comparison.json').write_text(json.dumps(rows,indent=2))
(r/'dropped-modules.json').write_text(json.dumps([n for n in order if n not in need],indent=2))
(dest/'MaskCNF.lean').write_text('''import MaskRUP
import InputLink
namespace Percolation.MaskRUP
theorem encode_cnf (v : Nat → Bool) (c : CNF.NClause) :
    Holds v (encode c) ↔ CNF.Holds v c := encode_holds v c
end Percolation.MaskRUP
''')
(dest/'EndpointR6.lean').write_text('''import Normalize
import MaskCNF
namespace Percolation
-- All certificate additions remain to be connected to the generator in round 6.
theorem not_conjecture20_mask_conditional (h : NormalizedCNFUnsat5) : ¬ Conjecture20 :=
  not_conjecture20_normalized h
#print axioms not_conjecture20_mask_conditional
end Percolation
''')
mods+=['MaskRUP','MaskCNF']+[f'MaskPilot{i:04d}' for i in range(0,5000,100)]+['EndpointR6']
(r/'packet/module-order.txt').write_text('\n'.join(mods)+'\n')
for n in ['guard.sh','replay.sh']:
 shutil.copyfile(r/n,r/'packet'/n)
print(len(mods),len(need))

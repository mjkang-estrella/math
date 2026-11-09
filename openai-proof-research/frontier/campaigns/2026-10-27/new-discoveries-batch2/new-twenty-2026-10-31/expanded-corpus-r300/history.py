exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
b=l.parent.parent;ids=set(map(str,json.loads((l/'reservation.json').read_text())['ids']));hits=[]
for f in b.rglob('results.json'):
 if l in f.parents:continue
 try:o=json.loads(f.read_text())
 except Exception:continue
 if isinstance(o,dict):
  for i in ids & set(o):hits.append({'path':str(f.resolve()),'id':i,'entry':o[i]})
(l/'history-keyed.json').write_text(json.dumps(hits,indent=2));print('Exact keyed matches',json.dumps(hits)[:9000])
pat=r'Snevily|Thi.ry|two.person.whist|projection.cones|tight.neighbor|longest.increasing.subsequence|Brockman|Raff|circuit.relation|Brualdi.Ryser'
r=subprocess.run(['rg','-n','-i','--glob','*.md',pat,str(b)],capture_output=True,timeout=45)
lines=[x for x in r.stdout.decode(errors='replace').splitlines() if str(l) not in x and '/sources/' not in x and '/extracted/' not in x and '/frozen' not in x]
(l/'history-family-hits.txt').write_text('\n'.join(lines)+'\n');print('Family hits', '\n'.join(lines)[:13000])

from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
B=P.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[('pi-fibonacci-minima-source-hypothesis-r312',n) for n in ['SUMMARY.md','disposition.json','MANIFEST.json','verification-receipt.json','verify_lane_pass.py']]
inputs += [('root-mathdb-breadth-intake-r316','coverage-delta.json'),('root-mathdb-next-breadth-r318','reserved-ids.json')]
(P/'frozen').mkdir(exist_ok=True)
bindings=[]
for lane,n in inputs:
 s=B/lane/n; d=P/'frozen'/f'{lane}--{n}'
 h=sha(s)
 if not d.exists(): d.write_bytes(s.read_bytes())
 assert sha(d)==h
 bindings.append({'original':str(s),'copy':str(d),'sha256':h})
(P/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
for n in ['disposition.json','MANIFEST.json','verification-receipt.json']:
 o=json.loads((P/'frozen'/f'pi-fibonacci-minima-source-hypothesis-r312--{n}').read_text())
 print(n,json.dumps(o)[:9500])

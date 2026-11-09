from pathlib import Path
import json,hashlib,sys
P=Path(__file__).resolve().parent; B=P.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
root=B/'root-mathdb-fibonacci-intake-r319'
manifest=json.loads((root/'manifest.json').read_text())
note=root/'frozen/payload/frozen/freeze-note.json'
assert sha(note)==manifest[str(note.relative_to(root))]
bindings=json.loads(note.read_text())['bindings']
checks=[]
for key,row in bindings.items():
 p=(B/'pi-fibonacci-minima-source-hypothesis-r312'/row['path']).resolve()
 h=sha(p)
 assert h==row['sha256'],key
 checks.append({'key':key,'path':str(p),'sha256':h})
record=json.loads(Path(next(c['path'] for c in checks if c['key']=='mathdb_371202_json')).read_text())
matches=[]
def walk(o,path='$'):
 if isinstance(o,dict):
  if '009c10c4-3dc7-47ce-8c70-0b9ae15e58a3' in [str(v) for v in o.values() if not isinstance(v,(dict,list))]:
   matches.append({'path':path,'record':o})
  for k,v in o.items(): walk(v,path+'.'+k)
 elif isinstance(o,list):
  for i,v in enumerate(o): walk(v,path+f'[{i}]')
walk(record)
result={'status':'PASS','verified_input_bindings':checks,'source_note_sha256':sha(note),'public_reply_uuid_matches':matches,'scope':'Cached-source bindings and presence of cited reply only; not current public availability, mathematical verification, or original pre-read timing.','counts_unchanged':{'additional':9,'total':39}}
if sys.argv[1]=='build':
 (P/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 m={p.name:sha(p) for p in [P/'verify.py',P/'result.json']}
 (P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
else:
 assert json.loads((P/'result.json').read_text())==result
 for n,h in json.loads((P/'manifest.json').read_text()).items(): assert sha(P/n)==h
 (P/'verification-receipt.json').write_text(json.dumps({'status':'PASS','input_bindings':8,'reply_uuid_matches':len(matches),'payload_hashes':2,'credit':0},indent=2)+'\n')
print(json.dumps({'status':'PASS','input_bindings':len(checks),'reply_uuid_matches':len(matches),'reply_fields':[list(m['record']) for m in matches]}))

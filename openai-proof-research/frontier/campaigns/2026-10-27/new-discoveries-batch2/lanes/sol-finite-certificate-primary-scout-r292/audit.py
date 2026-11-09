import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'bindings.json').read_text())
known={r['original'] for r in records}
missing=[str(p) for p in (L/'sources').iterdir() if str(p) not in known]
changed=[]
for r in records:
 for key in (['copy'] if r['kind']=='administrative' else ['original','copy']):
  p=pathlib.Path(r[key])
  if not p.exists() or sha(p)!=r['sha256']:changed.append([key,str(p)])
out=dict(bound_records=len(records),unbound_sources=missing,changed=changed)
(L/'pre-final-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

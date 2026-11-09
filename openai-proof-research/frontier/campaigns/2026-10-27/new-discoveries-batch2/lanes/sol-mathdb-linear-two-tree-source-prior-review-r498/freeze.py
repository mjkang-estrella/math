import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; lanes=L.parent; B=lanes.parent; I=lanes/'root-mathdb-three-candidate-intake-r493'; A=I/'frozen/claude-mathdb-primary-qualified-breadth-r480'; O=lanes/'claude-mathdb-primary-qualified-breadth-r480'
def bind(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
initial=[I/'manifest.json',I/'bindings.json',A/'manifest.json',A/'bindings.json',A/'retained-sources.json',B/'ledger.json',B/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/upstream.json')]
initial += [p for p in A.rglob('*') if p.is_file() and ('337963' in p.name or '1712.05883' in p.name)]
(L/'initial-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[bind(p) for p in initial if p.exists()]},indent=2)+'\n')
# Validate bytes and exact file set, independently; no upstream code execution.
m=json.loads((I/'manifest.json').read_text()); entries=m['files']; expected={x['path'] for x in entries}; excluded=set(m['excluded_exact_paths']); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}; errors=[]
for e in entries:
 p=I/e['path']; q=bind(p)
 if (q['sha256'],q['size'])!=(e['sha256'],e['size']):errors.append(e['path'])
assert actual-excluded==expected,(actual-excluded-expected,expected-actual)
assert not errors,errors
selected=[]
for p in initial:
 if p.exists() and p.is_relative_to(A):
  orig=O/p.relative_to(A)
  if orig.exists():
   a,b=bind(p),bind(orig);assert (a['sha256'],a['size'])==(b['sha256'],b['size']);selected.append({'copy':a,'original':b})
(L/'intake-validation.json').write_text(json.dumps({'PASS':True,'intake_files':len(entries),'exact_file_set':True,'direct_original_copy':selected,'upstream_verifiers_executed':False},indent=2)+'\n')
print(json.dumps({'PASS':True,'intake_files':len(entries),'selected':[str(p) for p in initial]}))

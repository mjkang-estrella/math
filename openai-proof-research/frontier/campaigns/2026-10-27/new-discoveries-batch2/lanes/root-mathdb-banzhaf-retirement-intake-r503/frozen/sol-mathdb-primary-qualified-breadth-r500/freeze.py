import pathlib,json,hashlib,shutil
O=pathlib.Path(__file__).resolve().parent; L=O.parent; B=L.parent; I=L/'root-mathdb-abelianisation-retirement-intake-r499'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def read(p):return json.loads(p.read_text())
def ref(p):return {'path':str(p.resolve()),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def check(p,e):
 r=ref(p); assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p);return r
refs=read(O/'initial-flat-bindings.json'); checked=[]
m=read(I/'manifest.json'); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}; assert actual=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:checked.append(check(I/e['path'],e))
for e in read(I/'bindings.json'):
 for key in ['original','copy']:checked.append(check(pathlib.Path(e[key]),e))
cm=read(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20
for e in chunks:checked.append(check(C/e['path'],e))
print('frozen_inputs schema',repr(cm['frozen_inputs'])[:6000])
for e in cm['frozen_inputs']:
 p=pathlib.Path(e['path']); p=p if p.is_absolute() else C/p
 checked.append(check(p,e))
assert len(cm['frozen_inputs'])==8
freeze=[I/n for n in ['DECISION.md','adjudications.json','coverage-delta.json','reserved-ids.json','queue.json','hypothesis-queue.json']]
for d in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 freeze += [p for p in (L/d).iterdir() if p.is_file() and (p.suffix in ['.json','.md']) and p.name not in ['manifest.json','verification-receipt.json']]
freeze += [B/'ledger.json',B/'prior-campaign-context.json']
for p in freeze:
 r=ref(p); refs.append(r); dest=O/'frozen'/p.parent.name/p.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);assert ref(dest)['sha256']==r['sha256']
refs+=checked+[ref(C/'manifest.json')]; unique={r['path']:r for r in refs}; (O/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
ids=read(I/'reserved-ids.json'); q=read(I/'queue.json'); print('queue shape',type(q).__name__); q=q if isinstance(q,list) else q['queue']; print('queue first keys',list(q[0])); assert len(q)==50 and {e['mathdb_id'] for e in q}==set(ids['ids']);assert len(set(ids['ids']))==50
cov=read(I/'coverage-delta.json');assert len(cov)==3683;assert not set(map(str,ids['ids']))&set(cov);assert ids['other_active_reservations']==[];assert not set(ids['ids'])&{338290,337963,372627,372628,368940,404067,364119,339564}
(O/'input-integrity.json').write_text(json.dumps({'status':'PASS','intake_exact_membership':True,'direct_bindings_checked':len(read(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'baseline':len(cov),'assigned':50,'other_active_reservations':0},indent=2)+'\n')
print('input integrity PASS')

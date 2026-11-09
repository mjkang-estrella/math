import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r713';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 a=binding(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p);return a
refs=[]
for n in ['manifest.json','bindings.json','queue-r714.json','reserved-ids-r714.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json']:refs.append(binding(I/n))
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:refs.append(check(I/e['path'],e))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:refs.append(check(pathlib.Path(e[k]),e))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:refs.append(check(C/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',*L.glob('*r363*/DECISION.md'),*L.glob('*r363*/manifest.json')]:refs.append(binding(p))
# Bind flat references but do not recursively follow historical trees.
f=L/'sol-mathdb-primary-qualified-breadth-r710/flat-bindings.json'
refs.append(binding(f))
raw=j(f)
refs.extend(check(pathlib.Path(e['path']),e) for e in raw)
cov=j(I/'coverage-delta.json');assert len(cov)==8733
reservations=j(I/'active-breadth-reservations.json');seen=set()
for r in reservations:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
q=j(I/'queue-r714.json');assert [x['mathdb_id'] for x in q]==reservations[-1]['ids']
unique={r['path']:r for r in refs};(P/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
(P/'pre-reading-checks.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_exact_payload=True,intake_pairs=len(j(I/'bindings.json')),original_chunks=20,frozen_inputs=8,coverage_baseline=len(cov),reservations=[dict(lane=r['lane'],count=len(r['ids'])) for r in reservations],disjoint=True,scientific_reading_started=False),indent=2)+'\n')
print('PRE-READING PASS',len(unique),'bindings')

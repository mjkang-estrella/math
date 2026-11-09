import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m),'manifest coverage mismatch'
for n,r in m.items():assert h(L/n)==r['sha256'] and (L/n).stat().st_size==r['bytes'],n
f=json.loads((L/'freeze-record.json').read_text())
count=0
for r in f['records']:
 assert h(L/r['copy'])==r['sha256']
 if r['kind']=='scientific':assert h(pathlib.Path(r['original']))==r['sha256'];count+=1
for r in json.loads((L/'access.json').read_text()):
 if 'sha256' in r:assert h(L/r['original'])==h(L/r['copy'])==r['sha256']
e=json.loads((L/'extraction.json').read_text());assert h(L/e['original'])==h(L/e['copy'])==e['text_sha256']
assert json.loads((L/'check-results.json').read_text())['status']=='PASS'
p=json.loads((L/'provenance.json').read_text());assert h(pathlib.Path(p['guard_path']))==p['guard_sha256']
r=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'manifest.json'),manifest_files=len(m),scientific_originals_rechecked=count,administrative_policy='snapshot hashes only; current administrative originals not required stable',separate_guarded_verification=True)
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

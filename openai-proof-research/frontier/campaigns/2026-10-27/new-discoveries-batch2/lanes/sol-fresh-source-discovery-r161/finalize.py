import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def rec(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
queries=[];keep=set()
for p in sorted(L.glob('history-query-*.json')):
 j=json.loads(p.read_bytes());queries.append(dict(file=p.name,sha256=sha(p.read_bytes()),pattern=j['pattern'],body_count=j['full_body_count'],hits=len(j['hits'])))
 if r'\bUlas\b' in j['pattern']:
  keep.update('history-'+h['sha256']+'.txt' for h in j['hits'])
removed=0
for p in (L/'sources').glob('history-*.txt'):
 if p.name not in keep:p.unlink();removed+=1
save('history-cleanup.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),removed_generated_reopened_echoes=removed,kept=sorted(keep),queries=queries,reason='Drop accidental formulas-substring body copies; preserve corrected query records and original source-role references. No originals removed.'))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
primary=[rec(L/'sources'/r['name']) for r in http if 'sha256' in r]
assert all(sha((L/'sources'/r['name']).read_bytes())==r['sha256'] for r in http if 'sha256' in r)
hist=json.loads((L/'history-receipt.json').read_bytes())
preserved=[dict(path=p,sha256=h,bytes=z) for p,h,z in hist['records'] if '/sol-fresh-source-discovery-r11' in p and any('/sol-fresh-source-discovery-r'+str(i)+'/' in p for i in [111,112,113])]
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),credit=0,counts=dict(additional=9,total=39,next=40),selected='Ulas 1909.10844v1 Conjecture4.2(3), all k>=2,n>=1',status='unresolved; no eligibility clearance',guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,limits='sampled process group, unsampled peaks possible'),primary=primary,http_failures=[r for r in http if 'error' in r],published_body='DOI redirects to no_subscription; revised scope unread',historical_originals_r111_r113=preserved,history_scope='Qualified r157/r158/r155 indexes plus changed/new original roles; full-body aliases, no global cutoff; no entire-lane exclusion',registry_scope='Current heads unchanged from r157; two older300-path gaps retained; no worldwide absence',source_searches=['"Strong arithmetic property of certain Stern polynomials" published','"Ulas" "p_{k,n}" roots conjecture','"Stern polynomials" "real roots" 2026 conjecture','"Stern" "Ulas" "Conjecture 4.2"'],procedural_failures=['nonexistent r157/history-delta path','initial Ulas substring/formulas noise','initial sparse formula missing (t-1); exact assertion failed; corrected'],public_mutations=False,git=False,children=False))
# No need to reproduce the unchanged full historical inventory in the handback.
q=L/'history-receipt.json';save('history-index-reference.json',dict(qualified_r157=str(L.parent/'sol-fresh-source-discovery-r157/history-receipt.json'),qualified_r157_sha256=hist['qualified_r157_sha256'],refreshed_full_body_count=len(hist['records']),temporary_refreshed_index_sha256=sha(q.read_bytes()),delta='history-delta.json',queries=queries));q.unlink()
excluded={'finalmanifest.json','scientific-freeze.json','verification.json'}
paths=sorted(p for p in L.rglob('*') if p.is_file() and p.name not in excluded)
payload=[rec(p) for p in paths]
science=[r for r in payload if not r['path'].startswith('context-')]
save('scientific-freeze.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='zero discovery; scientific records only',entries=science))
payload.append(rec(L/'scientific-freeze.json'));save('finalmanifest.json',dict(entries=payload,excludes=['itself','verification.json']))
fail=[]
for label in ['finalmanifest.json','scientific-freeze.json']:
 for r in json.loads((L/label).read_bytes())['entries']:
  if rec(L/r['path'])!=r:fail.append([label,r['path']])
save('verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),failures=fail,verified_manifest_entries=len(payload),verified_scientific_entries=len(science),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),freeze_sha256=sha((L/'scientific-freeze.json').read_bytes()),passed=not fail))
print((L/'verification.json').read_text());assert not fail

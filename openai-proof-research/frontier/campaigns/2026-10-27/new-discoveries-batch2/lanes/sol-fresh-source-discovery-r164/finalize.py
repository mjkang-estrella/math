import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def record(p):b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
if len(sys.argv)>1 and sys.argv[1]=='verify':
 checks=[]
 for n in ['finalmanifest.json','scientific-freeze.json']:
  j=json.loads((L/n).read_text())
  for r in j['files']:
   actual=record(L/r['path']);assert actual==r,(n,r['path']);checks.append([n,r['path']])
 j=json.loads((L/'provenance.json').read_text());g=Path(j['guard']['path']);assert sha(g.read_bytes())==j['guard']['sha256']
 result=dict(utc=now(),status='PASS',verified_bindings=len(checks),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),freeze_sha256=sha((L/'scientific-freeze.json').read_bytes()),limits='Byte integrity only; not a mathematical or eligibility proof')
 save('manifest-verification.json',result);print(json.dumps(result,indent=2));raise SystemExit
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
hist=json.loads((L/'history-receipt.json').read_text());guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
chron={}
for n in ['cif','log']:
 j=json.loads((L/'sources'/(n+'-history.json')).read_text())
 chron[n]=[dict(sha=x['sha'],author=x['commit']['author'],committer=x['commit']['committer'],message=x['commit']['message']) for x in j]
heads={n:json.loads((L/'sources'/(n+'-head.json')).read_text())['sha'] for n in ['omega','openai']}
save('provenance.json',dict(utc=now(),status='ZERO_CREDIT_UNRESOLVED_OR_PUBLICLY_EXCLUDED',credit=0,counts=dict(additional=9,total=39,next=40),primary_and_registry_http=http,local_source_bytes=[record(p) for p in sorted((L/'sources').iterdir()) if p.is_file()],heads=heads,path_last_change_chronology=chron,chronology_limit='last path change is not first publication; no worldwide priority claim',history=dict(bases=hist['bases'],records=len(hist['records']),changed=len(hist['changed_or_new']),hits=len(hist['hits']),r111_r113=hist['original_r111_r113'],scope='Full selected original disposition bodies scanned lexically, not universal semantic audit; copied aliases are not independent originals'),guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024*1024,group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,sampling_ms=40,unchanged=True),deviations=['Initial shell inventory and web search outside helper guard; documented in progress.md','Initial large context output truncated; targeted reads followed','Some original author-only matches reopened as bytes but not fully semantically assessed'],access_limits=['Inherited aa026->a19a and a19a->490f comparison path caps persist','No complete current Matkowski semantic eligibility clearance','No Lean execution or independent certification of external public proofs'],external_actions=False))
excluded={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
files=[record(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
save('scientific-freeze.json',dict(utc=now(),status='SCIENTIFIC_BYTES_FROZEN_ZERO_CREDIT',files=files,limits='No proof, acceptance or source eligibility PASS'))
files=[record(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}]
save('finalmanifest.json',dict(utc=now(),files=files,excluded_self_and_detached_receipt=True))
print('sealed',len(files),'paths; chronology',json.dumps(chron))

import json,hashlib,sys,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
excluded={'finalmanifest.json','manifest-verification.json','finalize-run.log','verify-run.log'}
if sys.argv[1]=='seal':
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_date='2026-10-29',retrieval_date_utc='2026-10-30',status='UNRESOLVED; no nomination',target='Kaneko full leaf-distance conjecture; 2411.06699v3 Conjecture3.1 / Filomat39:32 Conjecture1.2',primary_read_scope='Latest v3 definitions, conjecture, prior theorem statements and sufficient-condition proof setup; actual published companion statement and preliminary/proof interfaces; source-facing latest abstract and author publication page',primary_and_retrievals=http,source_files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted((L/'sources').iterdir())],history=['history-exact.json','history-leaf.json'],registry=['registry-screen.json','registry-deltas.json'],registry_limits='Both aa026->a19a and a19a->490f comparison files capped300; limited inherited current walks, no global clearance',omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',access_limits=['Original Kaneko proof unread403','EMMS2017 proof unread403; web/direct duplicate unsuccessful access','2007 host DNS failure; mirror404','Guessed DOI404 and wrong repository404 corrected'],web_search_scope=['strong geodetic title/conjecture navigation (old; abandoned)','Kaneko leaf-distance full proof/counterexample/current GitHub','Exact2411.06699 title and publication','EMMS exact title and current author publication page'],guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024*1024,groupRSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,qualification='Sampled group RSS does not bound unsampled transients; no cap raises'),scientific_claim='No full ordinary result. Route obstructions only; no prior-art or semantic clearance.'))
 science=[]
 for p in sorted(L.rglob('*')):
  if not p.is_file():continue
  rel=str(p.relative_to(L))
  if rel in excluded or rel=='scientific-freeze.json' or rel=='context-NEXT.md' or rel=='history-geodetic.json':continue
  if rel.startswith('reopened/') and not rel.startswith(('reopened/exact/','reopened/leaf/')):continue
  if p.suffix=='.log':continue
  science.append(dict(path=rel,sha256=sha(p),bytes=p.stat().st_size))
 save('scientific-freeze.json',dict(status='terminal no nominee',mutable_NEXT_excluded=True,exploratory_echoes_excluded=True,files=science))
 files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded]
 save('finalmanifest.json',dict(excluded=sorted(excluded),files=files))
j=json.loads((L/'finalmanifest.json').read_bytes());s=json.loads((L/'scientific-freeze.json').read_bytes())
for entry in j['files']+s['files']:
 p=L/entry['path'];assert p.stat().st_size==entry['bytes'] and sha(p)==entry['sha256'],entry['path']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual=={x['path'] for x in j['files']}
result=dict(verified=True,manifest_entries=len(j['files']),scientific_entries=len(s['files']),manifest_sha256=sha(L/'finalmanifest.json'),scientific_freeze_sha256=sha(L/'scientific-freeze.json'))
save('manifest-verification.json',result);print(json.dumps(result,indent=2))

from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
# Repair prose only; scientific formulas are unchanged.
p=L/'discovery.md';s=p.read_text().replace('diagnostics,+not','diagnostics,\nnot').replace('original-role records; only9 changed/new records required refreshing.\n1680 retained report paths were checked,','original-role records; initial9 changed/new records were refreshed.\nFinal surname/title refresh records1681 paths and10 changed/new records,').replace('the pendulum boundary-value problem. No reopened old target is renamed','the pendulum boundary-value problem. The final surname-complete refresh\nalso reopens r111 Costa entropy concavity, unrelated to this pendulum claim.\nNo reopened old target is renamed');p.write_text(s)
save('process-limits.json',dict(failures=['export.arxiv.org HTTP429 retained in http.jsonl; no retry','Initial listing search/q parameters ignored; hashes identical','One prose apply_patch failed to match a line; no mutation; repaired by this guarded script'],deviations=['Initial pwd/rg/head shell inventory not guarded','Expanded complete author screen after initial primary retrieval'],guard='unchanged helper_guard.py',sampling='nominal40ms; sampled process-group RSS/CPU may miss short peaks; RLIMIT_AS and RLIMIT_CPU additionally imposed'))
guard=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'sha256' in r:
  b=(L/'sources'/r['name']).read_bytes();assert sha(b)==r['sha256'];assert len(b)==r['bytes']
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_date='2026-10-29',primary_claim='1907.13009v1 Eq14, section4.4 Conjecture1',source_roles={'pendulum.html':'literal primary proof/conjecture body, v1','coupling.html':'literal primary, v1 Definition6 Conjecture11','orthomin.html':'latest observed primary v3, 2025-01-14, Proposition13 Theorem17 Conjecture12','omega-beta-result.cs':'current related public proof narrative','omega-beta-moment.cs':'current related proof mechanism','omega-beta-shape.cs':'current related public proof narrative','omega-beta-result.lean':'actual current formal proof body, read but not built','omega-beta-shape.lean':'actual current formal proof body, read but not built'},http=http,guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024*1024,group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1),heads={'omega':'d36a58e865e46580f127ef7a09d64ccbc2370296','openai':'4eaee87548250b2682affda7d05d947c05554bae'},eligibility='HOLD; zero credit; no independent review or complete publication-history clearance',limits=['aa026->a19a and a19a->490f300 capped coverage remains','No semantic absence guarantee from paths','No published-equivalence claim from failed Crossref title query','No universal proof from numerical checks','Process deviations in process-limits.json']))
exclude={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
records=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in exclude:records.append(dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
save('scientific-freeze.json',dict(schema=1,scope='All payload paths except self-referential manifests/verification',records=records))
records.append(dict(path='scientific-freeze.json',bytes=(L/'scientific-freeze.json').stat().st_size,sha256=sha((L/'scientific-freeze.json').read_bytes())))
save('finalmanifest.json',dict(schema=1,records=records))
checked=[]
for n in ['finalmanifest.json','scientific-freeze.json']:
 j=json.loads((L/n).read_text())
 for r in j['records']:
  b=(L/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
 checked.append(dict(manifest=n,verified=len(j['records']),sha256=sha((L/n).read_bytes())))
save('manifest-verification.json',dict(status='PASS',checks=checked));print(checked)

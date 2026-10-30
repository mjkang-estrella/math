from pathlib import Path
import json,hashlib,datetime
h=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(n,x):(h/n).write_text(json.dumps(x,indent=2)+'\n')
for p in [h.parent/'AGENTS.md',h/'AGENTS.md']:
 if p.exists():print('ADDITIONAL INSTRUCTION',str(p),p.read_text())
before=json.loads((h/'freeze-before.json').read_text());rows=[]
for x in before['scientific_pairs']:
 a=sha(Path(x['original']));b=sha(h/x['copy'])
 rows.append(dict(**x,original_after_sha256=a,copy_after_sha256=b,pass_unchanged=a==b==x['sha256']))
live=[]
for line in (h/'retrieval.jsonl').read_text().splitlines():
 x=json.loads(line)
 if 'sha256' in x:
  actual=sha(h/'live'/x['name']);live.append(dict(name=x['name'],retrieval_sha256=x['sha256'],after_sha256=actual,pass_unchanged=actual==x['sha256']))
write('freeze-after.json',dict(utc=now(),assigned_pairs=rows,live_retrievals=live,status='PASS' if all(x['pass_unchanged'] for x in rows+live) else 'FAIL',administration='Local snapshots only, no live mutable bindings'))
assert all(x['pass_unchanged'] for x in rows+live)
write('provenance.json',dict(utc=now(),reviewer='Solo review sub-agent; no children',recommendation='EXCLUDE from campaign credit as routine complete adaptation; root decides',gates=dict(SOURCE='PASS',MATH='PASS ordinary universal argument',SUBSTANTIVE='FAIL: complete adaptation given, eligibility judgment',NOVELTY='HOLD bounded coverage',FORMAL='Feasible in principle; no implementation or certification'),scientific_original_copy_pairs=len(rows),assigned_sources='75 top-level candidate/root records and candidate primary copies. Inherited original manifests are preserved documents, not independently reverified 2577-pair claims.',administrative_snapshots=['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md','ancestor.txt','guard.txt'],inputs='freeze-before.json',after='freeze-after.json',retrieval='retrieval.jsonl',comparison='comparison-evidence.json',diagnostics='checker.py and checker-evidence.json',failures='FAILURES.md; candidate original preserved',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),caps=dict(AS_MiB=512,sampled_group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),no_actions=['children','git','shared edits','browser','external messages/posts/uploads','MathDB edits','Lean','manuscript','counts'],novelty_limit='No exhaustive current/historical/public-registry or worldwide priority clearance; no parked reconstruction and no denied-route retry',manifest_exclusions=['final-manifest.json','final-verification.json']))
excluded=['final-manifest.json','final-verification.json']
files={str(p.relative_to(h)):sha(p) for p in sorted(h.rglob('*')) if p.is_file() and str(p.relative_to(h)) not in excluded}
write('final-manifest.json',dict(utc=now(),algorithm='SHA256',explicit_exclusions=excluded,files=files))
print(json.dumps(dict(status='PASS',assigned_pairs=len(rows),live_bodies=len(live),manifest_files=len(files))))

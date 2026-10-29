import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def put(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if len(sys.argv)>1 and sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_bytes());bad=[]
 for p,h in j['files'].items():
  f=L/p
  if not f.is_file() or sha(f.read_bytes())!=h:bad.append(p)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json','finalize.log'}}
 assert actual==set(j['files']),('inventory drift',actual^set(j['files']))
 assert not bad,bad
 result=dict(utc=utc(),status='PASS',entries=len(j['files']),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),bad=bad,exclusions=['finalmanifest.json','manifest-verification.json','finalize.log'])
 put('manifest-verification.json',result);print(result);sys.exit()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
hist=json.loads((L/'history-receipt.json').read_bytes())
required=[]
for n in [111,112,113]:
 ps=[p for p,h,s in hist['records'] if f'/sol-fresh-source-discovery-r{n}/' in p and Path(p).name.lower() in {'summary.md','discovery.md','proof.md'}]
 assert ps,n
 required.extend(ps)
put('original-r111-r113-receipt.json',dict(paths=required,coverage='complete named report bodies queried, original summaries explicitly read; no exclusions by lane number'))
inherited=[]
for n,filename in [(133,'history-receipt.json'),(133,'registry-delta-receipt.json'),(136,'freshness-receipt.json'),(137,'history-receipt.json'),(137,'registry-delta-receipt.json')]:
 p=L.parent/f'sol-fresh-source-discovery-r{n}'/filename
 inherited.append(dict(path=str(p),sha256=sha(p.read_bytes()),semantic_limit='Only previously documented bounded scope; not target clearance'))
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
checks=json.loads((L/'checks.json').read_bytes());assert checks['N']==5000 and checks['status']=='PASS'
put('provenance.json',dict(finalized_utc=utc(),outcome='zero nominees; source unresolved',counts=dict(additional=9,total=39,next=40),write_scope=str(L),guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,thread_env=1,unchanged=True,sampling_limit='Sampled /proc process-group RSS/CPU does not prove continuous peaks; tool-output guard receipts for some retrievals were not separately redirected to lane logs.'),http=http,inherited=inherited,history=dict(paths=len(hist['records']),new_changed=len(hist['changed']),full_body_lexical=True,global_hit_cutoff=None,semantic_limit='Exact target aliases no hit; broader collisions described in discovery.md; initial clipped historical display not claimed complete reading.'),searches=dict(clock_limit='Queries occurred during this turn; per-query UTC was not separately captured. HTTP observations have real UTC. No backdated search timestamp supplied.',queries=['algebra open question 2025 involution ring conjecture','conjecture 2026 numerical semigroups polynomial','conjecture commuting probability rings','conjecture 2024 finite fields permutation binomials','The genesis of a conjecture in number theory Heffernan','partition divides n! conjecture counterexample','Heffernan MacHale conjecture partitions','A046668 proof conjecture','Heffernan MacHale 2024 partition conjecture proof','A192885 negative','p(n) largest prime factor n conjecture','Heffernan genesis correction conjecture','On the largest prime factor of the partition function of n pdf'],limit='Bounded discovery/search leads; search absence is not novelty evidence.'),failures=[x for x in http if 'error' in x]+[dict(kind='registry-path-cap',detail='aa026 to a19a compare returns exactly300 paths; no completeness claim'),dict(kind='console-truncation',detail='Some concatenated old report displays clipped, disclosed; no semantic full-read claim for them')],checks=checks,remaining_gates=['full ordinary source resolution','target-specific current public proof-body screening including capped interval','classical/substantive independent adjudication','independent investment clearance before Lean or paper'],external_actions=False,children=False,git=False,browser_tabs=False,Lean=False,paper=False))
science={}
for p in sorted(L.rglob('*')):
 if p.is_file() and (p.parent.name=='sources' or p.name in {'SUMMARY.md','discovery.md','checks.py','checks.json','run-checks.sh'}):science[str(p.relative_to(L))]=sha(p.read_bytes())
put('scientific-freeze.json',dict(utc=utc(),files=science,excluded_mutable_context='context-NEXT.md and all context snapshots/receipts are historical context, not mathematical hypotheses; finalmanifest still binds all retained bytes'))
files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json','finalize.log'}}
put('finalmanifest.json',dict(utc=utc(),algorithm='sha256',files=files,exclusions=['self','manifest-verification.json','finalize.log (guard execution log)']))
print('frozen',len(files),'files; science',len(science))

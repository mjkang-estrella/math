from pathlib import Path
import hashlib,json,datetime,os
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(map(int,r))==set(ids)
chunks={};checks=[]
for i,o in r.items():
 p=o['provenance'];raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and raw.count(b'\n')==1;assert sha(raw)==p['raw_sha256'];obj=json.loads(raw);assert obj['statement']==o['statement'];assert sha(o['statement'].encode())==p['statement_utf8_sha256']
 c=Path(p['chunk'])
 if c not in chunks:chunks[c]=c.read_bytes();assert sha(chunks[c])==p['chunk_sha256']
 assert chunks[c].splitlines(keepends=True)[p['line_1based']-1]==raw;checks.append(i)
receipts=0
for p in (D/'sources').glob('*.receipt.json'):
 rec=json.loads(p.read_text())
 if rec.get('status')==200:
  q=Path(rec['path']);assert q.is_relative_to(D) and q.exists();assert sha(q.read_bytes())==rec['sha256'];receipts+=1
for name in ['omega-D5-tree.json','omega-Problems-tree.json']:
 o=json.loads((D/'sources'/name).read_text());assert o['truncated']==False
assert json.loads((D/'outputs/openai-cache-binding.json').read_text())['equal']
# /proc cwd check: never signal or inspect another lane's jobs.
jobs=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name) in (os.getpid(),os.getppid()):continue
 try:
  if Path(os.readlink(p/'cwd'))!=D:continue
  cmd=(p/'cmdline').read_bytes().replace(b'\x00',b' ').decode(errors='replace')
  if any(x in cmd for x in ['scripts/grid.py','scripts/game.py','scripts/xor.py','scripts/homology.py','scripts/prior_search.py','scripts/history.py','scripts/limited.py']):jobs.append({'pid':int(p.name),'cmd':cmd})
 except (OSError,PermissionError):pass
# Shell command containing this script's source may match text; actual executable commands only.
jobs=[j for j in jobs if j['cmd'].startswith(('python ','python3 '))]
assert not jobs,jobs
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_ID_keys':checks,'raw_chunk_statement_checks':'PASS','successful_fetch_receipts_verified':receipts,'registry_complete_scopes':'D5 and Problems; OpenAI cache subtree bound','formal_endpoint_count':0,'credit_requested':0,'lane_research_processes_remaining':jobs,'limitations':['No Lean packet or theorem','Numerical diagnostics are not formal proofs','Incomplete later-author/citing-paper coverage','Missing faithful descendent-matroid finite sweep','Wider all-campaign historical scan timed out']}
(D/'outputs/final-validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

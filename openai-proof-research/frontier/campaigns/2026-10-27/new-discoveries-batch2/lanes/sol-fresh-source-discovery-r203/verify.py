from pathlib import Path
import hashlib,json,datetime,subprocess,resource,os
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_excludes=['finalmanifest.json','verification-receipt.json'])
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']:assert os.environ[k]=='1'
assert resource.getrlimit(resource.RLIMIT_AS)[0]==536870912
assert resource.getrlimit(resource.RLIMIT_CPU)[0]==210
rows=json.loads((L/'primary-freeze.json').read_text());report['primary_pairs']=len(rows)
for x in rows:assert sha(Path(x['original']))==sha(L/x['copy'])==x['sha256'],x
x=json.loads((L/'guard-binding.json').read_text());assert sha(Path(x['original']))==sha(L/x['copy'])==x['sha256']
changed=[];rows=json.loads((L/'history-receipt.json').read_text())['records']
for x in rows:
 assert sha(L/x['copy'])==x['sha256']
 p=Path(x['original'])
 if not p.exists() or sha(p)!=x['sha256']:changed.append(x['original'])
report['reference_snapshot_copies']=len(rows);report['mutable_reference_changes']=changed
aliases=json.loads((L/'legacy-alias-refresh.json').read_text())['records']
for x in aliases:assert sha(L/x['copy'])==x['sha256']
report['inherited_alias_copies']=len(aliases)
r=subprocess.run(['python',str(L/'checks.py')],capture_output=True,text=True,check=True)
assert r.stdout==(L/'checks.json').read_text();report['exact_replay']='byte-identical'
assert not (L/'PROOF.md').exists()
m=json.loads((L/'finalmanifest.json').read_text());assert m['excludes']==report['manifest_excludes']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in m['excludes']}
assert actual==set(m['files'])
for n,h in m['files'].items():assert sha(L/n)==h,n
report['manifest_files']=len(actual)
(L/'verification-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))

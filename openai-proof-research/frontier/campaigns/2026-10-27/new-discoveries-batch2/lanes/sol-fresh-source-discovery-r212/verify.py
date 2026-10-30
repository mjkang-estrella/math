from pathlib import Path
import hashlib,json,subprocess,sys,datetime,os
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']:assert os.environ[k]=='1'
m=json.loads((L/'manifest.json').read_text());excluded={'manifest.json','verification-receipt.json'}
assert set(m['excluded'])==excluded
files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-excluded
assert files==set(m['files'])
for n,h in m['files'].items():assert H(L/n)==h,n
bindings=json.loads((L/'bindings.json').read_text())
for r in bindings:
 assert H(Path(r['original']))==r['sha256'],r['original']
 assert H(Path(r['copy']))==r['sha256'],r['copy']
refs=0
for fn in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((L/fn).read_text())['records']:
  assert H(Path(r['snapshot_reference']))==r['sha256'],r['snapshot_reference'];refs+=1
scientific=[]
for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
 if 'sha256' in r:
  assert H(L/'sources'/r['name'])==r['sha256']
  assert H(L/'frozen'/r['name'])==r['sha256']
  scientific.append({'name':r['name'],'sha256':r['sha256'],'original_copy_before_after':True})
 if 'failure_sha256' in r:assert H(L/'failures'/(r['name']+'.body'))==r['failure_sha256']
for name in ['karam','lim']:
 q=subprocess.run(['pdftotext','-layout',str(L/'frozen'/(name+'.pdf')),'-'],capture_output=True,check=True)
 assert q.stdout==(L/(name+'.txt')).read_bytes()
 assert q.stderr==(L/'receipts'/(name+'.extract.stderr')).read_bytes()
q=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,check=True)
assert q.stdout==(L/'receipts/checks.stdout').read_bytes()
assert q.stderr==(L/'receipts/checks.stderr').read_bytes()
# Recheck entire manifest after replays: replay must not mutate any manifest member.
for n,h in m['files'].items():assert H(L/n)==h,n
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':H(L/'manifest.json'),'files':len(files),'assigned_guard_bindings':len(bindings),'historical_snapshot_references':refs,'scientific':scientific,'exact_pdf_extraction_replay':True,'exact_checker_stdout_stderr_replay':True,'administrative_live_bindings':False,'excluded':sorted(excluded)}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

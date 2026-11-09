from pathlib import Path
import json,hashlib,subprocess,tempfile,shutil,datetime
L=Path(__file__).resolve().parent
def sig(p):
 b=p.read_bytes();return {'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def manifest():
 m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[sig(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']]};(L/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
# Freeze provisional exact payload for bounded rejection tests on copies of our own lane only.
manifest();results=[]
with tempfile.TemporaryDirectory(prefix='negative-',dir=L) as temp:
 T=Path(temp)
 for p in L.iterdir():
  if p.is_file():shutil.copyfile(p,T/p.name)
 p=T/'SUMMARY.md';b=p.read_bytes()
 for mode in ['hash','size','extra']:
  p.write_bytes(b)
  extra=T/'unexpected.txt'
  if extra.exists():extra.unlink()
  if mode=='hash':p.write_bytes(bytes([b[0]^1])+b[1:])
  elif mode=='size':p.write_bytes(b+b'!')
  else:extra.write_text('extra')
  r=subprocess.run(['python3','-B',str(L/'verify.py'),str(T)],capture_output=True,text=True)
  assert r.returncode!=0,(mode,r.stdout)
  expected={'hash':'HASH','size':'SIZE','extra':'EXTRA_OR_MISSING'}[mode];assert expected in r.stderr,(mode,r.stderr)
  results.append({'mutation':mode,'exit':r.returncode,'expected_rejection':expected,'stderr_tail':r.stderr.splitlines()[-1]})
(L/'negative-tests.json').write_text(json.dumps({'scope':'Own payload copies only, deleted after tests; no original mutation.','tests':results},indent=2)+'\n')
manifest()
r=subprocess.run(['python3','-B',str(L/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
s=sig(L/'manifest.json');receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':s['sha256'],'manifest_size':s['size'],'verification':json.loads(r.stdout),'negative_tests':results,'guard':'Executed by fixed helper_guard.py under 512MiB AS/groupRSS,CPU210s,wall230s; unchanged.','science':'No mathematical or novelty PASS. Zero credit and proposals.'}
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

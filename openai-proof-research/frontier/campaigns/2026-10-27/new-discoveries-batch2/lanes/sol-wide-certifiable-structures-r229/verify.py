"""Separate read/verify invocation after all packet writes; no finalizer import."""
import pathlib,json,hashlib,subprocess,os
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text())
errors=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
if actual!=set(m['files']):errors.append('file inventory mismatch')
for p,s in m['files'].items():
 if h(L/p)!=s:errors.append('manifest:'+p)
for b in json.loads((L/'frozenbindings.json').read_text()):
 if h(pathlib.Path(b['original']))!=b['sha256']:errors.append('original changed:'+b['original'])
 if h(pathlib.Path(b['copy']))!=b['sha256']:errors.append('copy changed:'+b['copy'])
before=h(L/'checks.json')
r=subprocess.run(['python',str(L/'checks.py')],capture_output=True,text=True,timeout=25,env=os.environ.copy())
if r.returncode or h(L/'checks.json')!=before:errors.append('diagnostic replay mismatch')
if 'finalmanifest.json' in m['files'] or 'verification-receipt.json' in m['files']:errors.append('manifest exclusion failure')
receipt={'pass':not errors,'errors':errors,'manifest_sha256':h(L/'finalmanifest.json'),'manifest_files':len(m['files']),
 'diagnostic_exit':r.returncode,'diagnostic_stdout':r.stdout.strip(),'checks_sha256':before,
 'scope':'Artifact integrity, frozen original/copy hashes and exact diagnostic replay only; not discovery proof, novelty clearance or pre-read-freeze certification.'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));raise SystemExit(bool(errors))

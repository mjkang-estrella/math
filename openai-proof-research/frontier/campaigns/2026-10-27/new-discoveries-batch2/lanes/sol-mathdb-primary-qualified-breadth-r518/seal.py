from pathlib import Path
import json,hashlib,subprocess,sys,datetime
P=Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
m=dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files)
(P/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
results=[]
for case in [None,'hash','size','extra']:
 args=[sys.executable,'-B',str(P/'verify.py')]+(['--negative',case] if case else [])
 r=subprocess.run(args,capture_output=True,text=True);assert r.returncode==(1 if case else 0),(case,r.stdout,r.stderr)
 results.append(dict(case=case or 'normal',exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
b=(P/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),integrity='PASS',scientific_acceptance=False,tests=results,negative_mutations='Expected values/file set changed in memory only; no originals mutated')
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

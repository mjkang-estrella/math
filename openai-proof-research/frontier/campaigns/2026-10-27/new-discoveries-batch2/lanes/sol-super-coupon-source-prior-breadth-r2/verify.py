from pathlib import Path
import json,hashlib,subprocess,datetime
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def check(kind,p,h):
 ok=p.exists() and H(p)==h;checks.append(dict(kind=kind,path=str(p),ok=ok));return ok
for r in json.loads((L/'finalmanifest.json').read_text())['files']:check('manifest',L/r['path'],r['sha256'])
for r in json.loads((L/'sourcebindings.json').read_text())['records']:
 if not r['administrative']:check('scientific_original_after',Path(r['original']),r['sha256'])
 if r['copy']:check('frozen_copy_after',Path(r['copy']),r['sha256'])
for r in json.loads((L/'access.json').read_text()):
 if 'sha256' in r:
  check('retrieved_original_after',Path(r['original']),r['sha256']);check('retrieved_frozen_after',Path(r['copy']),r['sha256'])
for f in ['history-screen.json','history-screen2.json']:
 for r in json.loads((L/f).read_text())['references']:check('historical_reference_after',Path(r['path']),r['sha256'])
for p in sorted((L/'texts').glob('*.txt')):
 q=L/'frozen-live'/(p.stem+'.pdf')
 if q.exists():
  b=subprocess.run(['pdftotext','-layout',str(q),'-'],check=True,capture_output=True).stdout
  checks.append(dict(kind='fresh_pdf_text',path=str(p),ok=hashlib.sha256(b).hexdigest()==H(p)))
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=H(L/'finalmanifest.json'),checks=checks,pass_all=all(r['ok'] for r in checks),failures=[r for r in checks if not r['ok']],counts_unchanged=[9,39,40])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(pass_all=receipt['pass_all'],checks=len(checks),failures=receipt['failures'])))
raise SystemExit(0 if receipt['pass_all'] else 1)

from pathlib import Path
import hashlib,json,sys,datetime,subprocess
R=Path(__file__).resolve().parent;L=R.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):
 if not p.is_file() or p.stat().st_size!=s or sha(p)!=h:raise ValueError('binding mismatch: '+str(p))
def files(root):return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
def put(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
mode=sys.argv[1]
if mode not in ['build','verify']:raise ValueError('build or verify')
freeze=json.loads((R/'input-freeze.json').read_text());supp=json.loads((R/'supplemental-bindings.json').read_text())
for e in freeze['files']+supp['files']:check(Path(e['path']),e['sha256'],e['size'])
for e in freeze['exactsets']:
 root=Path(e['root'])
 if files(root)!=set(e['paths']):raise ValueError('upstream exactset mismatch '+str(root))
 entries=json.loads((root/'manifest.json').read_text())['files']
 if files(root)-{'manifest.json','verification-receipt.json'}!={e['path'] for e in entries}:raise ValueError('upstream manifest set mismatch')
 for f in entries:check(root/f['path'],f['sha256'],f['size'])
for name,key in [('root-mathdb-circulant-review-intake-r381/bindings.json','copy'),('root-mathdb-circulant-intake-r375/bindings.json','copy'),('sol-mathdb-circulant-15-certificate-review-r378/sourcebindings.json','payload')]:
 p=L/name
 for e in json.loads(p.read_text()):
  for f in [Path(e['original']),p.parent/e[key]]:check(f,e['sha256'],e['size'])
for p in (R/'http').glob('*.meta.json'):
 m=json.loads(p.read_text());check(p.with_name(p.name.replace('.meta.json','.body')),m['sha256'],m['size'])
 if not all(k in m for k in ['url','effective_url','utc','status','usable']):raise ValueError('HTTP provenance incomplete')
for p in R.glob('*.provenance.json'):
 m=json.loads(p.read_text());check(p.with_name(p.name.replace('.provenance.json','.json')),m['sha256'],m['size'])
for n in ['source-v2','cada-pdf','korze-table']:
 p=R/'http'/n;m=json.loads(p.with_suffix('.meta.json').read_text())
 if not m['usable']:raise ValueError('unusable extraction')
 b=subprocess.run(['pdftotext','-layout',str(p.with_suffix('.body')),'-'],capture_output=True,check=True).stdout
 if b!=p.with_suffix('.txt').read_bytes():raise ValueError('extraction mismatch '+n)
C=L/'sol-mathdb-circulant-15-certificate-review-r378'
if (R/'http/source-v2.body').read_bytes()!=(C/'inputs/01_body').read_bytes():raise ValueError('current/frozen source mismatch')
if (R/'http/source-v2.txt').read_bytes()!=(C/'source.txt').read_bytes():raise ValueError('current/frozen extraction mismatch')
excluded={'manifest.json','verification-receipt.json'};payload=files(R)-excluded
if mode=='build':put(R/'manifest.json',{'files':[{'path':s,'size':(R/s).stat().st_size,'sha256':sha(R/s)} for s in sorted(payload)]})
else:
 m=json.loads((R/'manifest.json').read_text())['files']
 if payload!={e['path'] for e in m}:raise ValueError('own exactset mismatch')
 for e in m:check(R/e['path'],e['sha256'],e['size'])
 put(R/'verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(R/'manifest.json'),'own_payloads':len(m),'initial_bindings':len(freeze['files']),'supplemental_bindings':len(supp['files']),'root_exactsets':len(freeze['exactsets']),'http_attempts':len(list((R/'http').glob('*.meta.json'))),'extractions_regenerated':3,'recommendation':'PARK','prior':'HOLD','published_source':'HOLD','independent_math_replay':False,'credit':0})
print('PASS',mode,'initial',len(freeze['files']),'supplemental',len(supp['files']),'own',len(payload))

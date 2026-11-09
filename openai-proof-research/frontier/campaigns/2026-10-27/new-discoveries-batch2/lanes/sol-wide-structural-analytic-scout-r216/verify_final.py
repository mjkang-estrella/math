from pathlib import Path
import hashlib,json,subprocess,sys,datetime,runpy

p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
errors=[]
counts={}
def require(test,msg):
    if not test:errors.append(msg)

m=json.loads((p/'manifest.json').read_text())
excluded={'manifest.json','verification-receipt.json'}
actual={str(x.relative_to(p)) for x in p.rglob('*') if x.is_file() and str(x.relative_to(p)) not in excluded}
require(set(m['files'])==actual,'manifest file set mismatch')
require(set(m['excluded'])==excluded,'manifest exclusions mismatch')
for name,h in m['files'].items():
    require(sha((p/name).read_bytes())==h,'manifest hash '+name)

bindings=json.loads((p/'frozen-inputs.json').read_text())
bindings.append(json.loads((p/'history-index-binding.json').read_text()))
for r in bindings:
    for k in ['original','copy']:
        q=Path(r[k]);require(q.exists() and sha(q.read_bytes())==r['sha256'],'binding '+str(q))
counts['selected_bindings']=len(bindings)
index=json.loads((p/'frozen/history-index.json').read_text())
for r in index['records']:
    for k in ['original','snapshot_reference']:
        q=Path(r[k]);require(q.exists() and sha(q.read_bytes())==r['sha256'],'history '+str(q))
counts['inherited_original_snapshot_pairs']=len(index['records'])

receipts=[json.loads(s) for s in (p/'http.jsonl').read_text().splitlines()]
pdfs=list((p/'sources').glob('*.pdf'))
for q in pdfs:
    c=p/'work'/q.name
    h=sha(q.read_bytes())
    require(sha(c.read_bytes())==h,'source/work '+q.name)
    require(any(r.get('sha256')==h and '/pdf/' in r['url'] for r in receipts),'URL hash receipt '+q.name)
    z=subprocess.run(['pdftotext','-layout',str(c),'-'],capture_output=True,check=True)
    require(z.stdout==c.with_suffix('.txt').read_bytes(),'extraction '+q.name)
counts['source_work_pdf_pairs_and_extracts']=len(pdfs)
namespace=runpy.run_path(str(p/'checks.py'),run_name='verification_import')
expected=json.loads((p/'check-results.json').read_text())
require(namespace['main']()==expected,'exact control replay')
# Recheck manifest after replay, and explicitly report administrative nonbindings.
for name,h in m['files'].items():require(sha((p/name).read_bytes())==h,'postreplay '+name)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',errors=errors,counts=counts,manifest_sha256=sha((p/'manifest.json').read_bytes()),excluded=sorted(excluded),administrative_live_bindings=False,meaning='integrity and deterministic controls only; no acceptance or novelty certification')
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
sys.exit(bool(errors))

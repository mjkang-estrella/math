from pathlib import Path
import hashlib,json,datetime
b=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((b/'manifest.json').read_text())
assert set(m['excluded'])=={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(b)) for p in b.rglob('*') if p.is_file() and str(p.relative_to(b)) not in m['excluded']}
assert actual==set(m['files']), 'inventory mismatch'
for p,h in m['files'].items():assert sha(b/p)==h,p
originals=copies=0
for x in json.loads((b/'input-bindings.json').read_text())['files']:
    assert sha(b/x['copy'])==x['sha256'],x['copy'];copies+=1
    if x['verify_live_original']:
        assert sha(Path(x['original']))==x['sha256'],x['original'];originals+=1
assert json.loads((b/'check-results.json').read_text())['status']=='PASS'
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(b/'manifest.json'),'manifest_files':len(actual),'frozen_copies_checked':copies,'scientific_and_rule_originals_checked':originals,'live_mutable_administrative_originals_checked':False,'exclusions':m['excluded'],'scope':'Integrity verification after final writes; not a formal proof or novelty certificate.'}
(b/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))

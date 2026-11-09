from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent;F=D/'frozen';C=D.parent/'pi-subtraction-nim-source-hypothesis-r325'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(p.read_text())
def checks():
    bindings=read(D/'bindings.json')
    for r in bindings:
        assert sha(Path(r['original']))==r['sha256']
        assert sha(D/r['copy'])==r['sha256']
    child=read(F/'manifest.json')['files'];assert len(child)==31
    for r in child:
        assert sha(F/r['path'])==r['sha256']
        assert (F/r['path']).stat().st_size==r['bytes']
    assert {str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}=={r['path'] for r in child}|{'manifest.json','verification-receipt.json'}
    prov=read(F/'sources/provenance.json')
    for r in prov['frozen_input_bindings']:assert sha(C/r['path'])==r['sha256']
    rec=prov['cached_mathdb_record'];assert sha(Path(rec['path']))==rec['sha256']
    for r in prov['fetches']:assert sha(F/r['file'])==r['sha256']
    return {'bindings':len(bindings),'child_payloads':len(child),'external_bindings':len(prov['frozen_input_bindings'])+1,'fetched_source_bindings':len(prov['fetches'])}
def files():return sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','verification-receipt.json'})
if sys.argv[1]=='build':
    checks();(D/'manifest.json').write_text(json.dumps([{'path':str(p.relative_to(D)),'sha256':sha(p)} for p in files()],indent=2)+'\n')
else:
    result=checks();rows=read(D/'manifest.json')
    assert {r['path'] for r in rows}=={str(p.relative_to(D)) for p in files()}
    for r in rows:assert sha(D/r['path'])==r['sha256']
    result.update(result='PASS',root_payloads=len(rows),scope='Delivered-byte integrity and source bindings, not independent proof or original chronology')
    (D/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

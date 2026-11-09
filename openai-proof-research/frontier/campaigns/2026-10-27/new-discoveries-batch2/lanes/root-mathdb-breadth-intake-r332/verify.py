from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent; F=D/'frozen';B=D.parent
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
    child=read(F/'manifest.json')['files'];assert len(child)==61
    for r in child:
        assert sha(F/r['path'])==r['sha256']
        assert (F/r['path']).stat().st_size==r['bytes']
    assert {str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}=={r['path'] for r in child}|{'manifest.json','verification-receipt.json'}
    sources=read(F/'work/source-bindings.json');assert len(sources)==26
    for r in sources:assert sha(F/r['file'])==r['sha256']
    corpus=read(F/'work/corpus-verification.json');assert len(corpus)==20
    for r in corpus:assert sha(B/'pi-mathdb-full-corpus-inventory-r301'/r['path'])==r['sha256']
    old=read(F/'frozen/coverage-delta.json');new=read(F/'dispositions.json')['dispositions']
    reserved=read(F/'frozen/reserved-ids.json')
    assert len(old)==183 and len(new)==50 and len(set(reserved))==50
    assert set(new)==set(map(str,reserved)) and not set(old)&set(new)
    assert sha(B/'root-mathdb-breadth-intake-r326/coverage-delta.json')==sha(F/'frozen/coverage-delta.json')
    assert sha(B/'root-mathdb-breadth-intake-r326/reserved-ids.json')==sha(F/'frozen/reserved-ids.json')
    merged=dict(old)
    for i,r in new.items():merged[i]={'record_statement_review':'delegate_reported_complete','report':'pi-mathdb-primary-qualified-breadth-r327/dispositions.json','disposition':r['disposition'],'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
    assert len(merged)==233
    return merged,{'root_bindings':len(bindings),'child_payloads':61,'source_bindings':26,'corpus_hashes_rechecked':20}
def files():return sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','verification-receipt.json'})
if sys.argv[1]=='build':
    merged,_=checks();(D/'coverage-delta.json').write_text(json.dumps(merged,indent=2,sort_keys=True)+'\n')
    (D/'manifest.json').write_text(json.dumps([{'path':str(p.relative_to(D)),'sha256':sha(p)} for p in files()],indent=2)+'\n')
else:
    merged,result=checks();assert read(D/'coverage-delta.json')==merged
    rows=read(D/'manifest.json');assert {r['path'] for r in rows}=={str(p.relative_to(D)) for p in files()}
    for r in rows:assert sha(D/r['path'])==r['sha256']
    result.update(result='PASS',root_payloads=len(rows),reported_statement_reviews=233,scope='Integrity/coverage only; candidate not mathematically reviewed')
    (D/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

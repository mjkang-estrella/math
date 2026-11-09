from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
F=D/'frozen/pi-rainbow-path-replication-hypothesis-r317'
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
    child=read(F/'manifest.json')['files']
    assert len(child)==22
    for rel,h in child.items():assert sha(F/rel)==h
    assert {str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}==set(child)|{'manifest.json','verification-receipt.json'}
    n=0
    for line in (F/'inputs/input-hashes.txt').read_text().splitlines():
        h,rel=line.split('  ',1);assert sha(D.parent/rel)==h;n+=1
    assert n==8
    return {'bindings':len(bindings),'child_payloads':len(child),'external_bindings':n}
def files():return sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','verification-receipt.json'})
if sys.argv[1]=='build':
    checks()
    (D/'manifest.json').write_text(json.dumps([{'path':str(p.relative_to(D)),'sha256':sha(p)} for p in files()],indent=2)+'\n')
else:
    result=checks();rows=read(D/'manifest.json')
    assert {r['path'] for r in rows}=={str(p.relative_to(D)) for p in files()}
    for r in rows:assert sha(D/r['path'])==r['sha256']
    result.update(result='PASS',root_payloads=len(rows),scope='Delivered-byte integrity, not proof or original verification chronology')
    (D/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

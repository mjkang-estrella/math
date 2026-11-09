from pathlib import Path
import json, hashlib, sys, datetime
R=Path(__file__).resolve().parent
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())['bindings']
for e in bindings:
    for p in [Path(e['original']),R/e['copy']]:
        assert h(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
C=R/'frozen'; m=json.loads((C/'review-manifest.json').read_text())
listed={e['path'] for e in m['files']}
actual={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}
assert actual-set(m['excluded_by_exact_relative_name'])==listed
for e in m['files']:
    p=C/e['path'];assert h(p)==e['sha256'] and p.stat().st_size==e['bytes'],str(p)
refs=json.loads((C/'work/frozen-delivery-manifest.json').read_text())['checked']
base=R.parent/'root-mathdb-breadth-intake-r332/frozen'
for e in refs:
    p=base/e['path'];assert h(p)==e['sha256'] and p.stat().st_size==e['bytes'],str(p)
ex={'manifest.json','verification-receipt.json'}
def payload(): return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-ex
if sys.argv[1]=='build':
    save('manifest.json',{'files':[{'path':p,'sha256':h(R/p),'size':(R/p).stat().st_size} for p in sorted(payload())]})
elif sys.argv[1]=='verify':
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:
        p=R/e['path'];assert h(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
    save('verification-receipt.json',{'status':'PASS','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_copy_bindings':len(bindings),'review_payloads':len(listed),'upstream_references':len(refs),'root_payloads':len(own),'mathematical_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(bindings),'bindings',len(refs),'upstream references')

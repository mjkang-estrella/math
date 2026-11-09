from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/sol-mathdb-circulant-15-certificate-review-r378'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries:check(C/e['path'],e['sha256'],e['size'])
refs=json.loads((C/'sourcebindings.json').read_text())
for e in refs:
    check(Path(e['original']),e['sha256'],e['size']);check(C/e['payload'],e['sha256'],e['size'])
I=L/'root-mathdb-circulant-intake-r375'
freeze=json.loads((C/'freeze.json').read_text())
assert sha(I/'manifest.json')==freeze['intake_manifest_sha256']
upstream=json.loads((I/'manifest.json').read_text())['files']
for e in upstream:check(I/e['path'],e['sha256'],e['size'])
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'source_pairs':len(refs),'upstream_payloads':len(upstream),'independent_math_replay':False,'acceptance':'HOLD','credit':0})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(entries),'child payloads',len(refs),'source pairs',len(upstream),'intake originals')

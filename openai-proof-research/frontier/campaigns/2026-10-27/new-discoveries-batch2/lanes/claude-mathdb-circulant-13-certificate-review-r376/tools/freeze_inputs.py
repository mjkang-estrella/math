# Freeze (hash-only, flat references) the r375 intake and r360 originals before reading scientific content.
import hashlib,json,sys,datetime
from pathlib import Path
L=Path(sys.argv[1]).resolve(); I=Path(sys.argv[2]).resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=[]
def chk(p,h,s,tag):
    if not p.is_file(): fail.append((tag,str(p),'missing')); return
    if p.stat().st_size!=s or sha(p)!=h: fail.append((tag,str(p),'mismatch'))
man=json.loads((I/'manifest.json').read_text())['files']
for e in man: chk(I/e['path'],e['sha256'],e['size'],'intake-manifest')
actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if actual!={e['path'] for e in man}: fail.append(('intake-manifest','set',sorted(actual^{e['path'] for e in man})))
b=json.loads((I/'bindings.json').read_text())
for e in b:
    chk(Path(e['original']),e['sha256'],e['size'],'binding-original'); chk(I/e['copy'],e['sha256'],e['size'],'binding-copy')
C=I/'frozen/claude-mathdb-primary-qualified-breadth-r360'
cm=json.loads((C/'manifest.json').read_text())['files']
for e in cm: chk(C/e['path'],e['sha256'],e['size'],'r360-manifest')
cset={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if cset!={e['path'] for e in cm}: fail.append(('r360-manifest','set',sorted(cset^{e['path'] for e in cm})))
# originals of r360 payloads (author lane, immutable)
O=L.parent/'claude-mathdb-primary-qualified-breadth-r360'
for e in cm: chk(O/e['path'],e['sha256'],e['size'],'r360-original')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_dir':str(I),'r360_original_dir':str(O),
 'intake_manifest_sha256':sha(I/'manifest.json'),'intake_receipt_sha256':sha(I/'verification-receipt.json'),
 'r360_manifest_sha256':sha(C/'manifest.json'),'counts':{'intake_manifest':len(man),'bindings':len(b),'r360_payloads':len(cm)},
 'refs':[{'path':str(I/e['path']),'sha256':e['sha256'],'size':e['size']} for e in man],
 'r360_original_refs':[{'path':str(O/e['path']),'sha256':e['sha256'],'size':e['size']} for e in cm],
 'failures':fail,'status':'PASS' if not fail else 'FAIL'}
(L/'input-bindings.json').write_text(json.dumps(out,indent=1,sort_keys=True)+'\n')
print(out['status'],out['counts'],len(fail)); sys.exit(1 if fail else 0)

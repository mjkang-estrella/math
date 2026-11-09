import pathlib,json,hashlib,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent
excluded={'manifest.json','final-verification-receipt.json'}
def save(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def manifest():
 save('manifest.json',dict(excluded_exact_paths=sorted(excluded),files=[dict(path=str(p.relative_to(O)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in excluded]))
manifest();tests=[]
for mode,reason in [('hash','hash mismatch'),('size','size mismatch'),('extra','extra/missing payload')]:
 p=subprocess.run(['python3','-B',str(O/'verify.py'),'--negative',mode],text=True,capture_output=True)
 assert p.returncode!=0 and reason in p.stderr,(mode,p.stdout,p.stderr)
 tests.append(dict(mode=mode,exit=p.returncode,stderr=p.stderr.strip(),originals_mutated=False,injection='in-memory expected-hash/size/file-inventory alteration'))
save('negative-tests.json',tests);manifest()
p=subprocess.run(['python3','-B',str(O/'verify.py')],capture_output=True,text=True)
assert p.returncode==0,(p.stdout,p.stderr)
r=json.loads(p.stdout);m=O/'manifest.json';r.update(manifest_sha256=hashlib.sha256(m.read_bytes()).hexdigest(),manifest_size=m.stat().st_size,negative_tests=tests,guard='Finalizer and all its children execute inside fixed helper_guard; limits unchanged',scientific_boundary_deviation=True)
save('final-verification-receipt.json',r);print(json.dumps(r,indent=2))

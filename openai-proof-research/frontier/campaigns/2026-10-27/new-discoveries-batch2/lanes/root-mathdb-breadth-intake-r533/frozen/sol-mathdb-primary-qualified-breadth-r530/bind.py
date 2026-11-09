import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-ordinal-exclusion-intake-r529'
def sig(p):
 b=p.read_bytes(); return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(p):return json.loads(p.read_text())
refs={}
def bind(p,expected=None):
 p=p.resolve(); s=sig(p)
 if expected: assert all(s[k]==expected[k] for k in s),(str(p),s,expected)
 refs[str(p)]=s
for p in I.glob('*.json'):bind(p)
m=read(I/'manifest.json')
expected={x['path'] for x in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
assert actual==expected
for x in m['files']:bind(I/x['path'],x)
for x in read(I/'bindings.json'):
 bind(pathlib.Path(x['original']),x);bind(pathlib.Path(x['copy']),x)
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
print('intake exact payload and original/copy pairs checked',len(refs))
for f in ['queue.json','reserved-ids.json','active-breadth-reservations.json']:
 v=read(I/f);print(f,json.dumps(v,ensure_ascii=False)[:6500])
r=L/'pi-mathdb-full-corpus-inventory-r301'/'manifest.json';bind(r)
print('r301 schema',json.dumps(read(r),ensure_ascii=False)[:9000])
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')

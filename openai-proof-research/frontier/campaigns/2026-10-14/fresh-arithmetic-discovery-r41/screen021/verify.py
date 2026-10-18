import pathlib,json,hashlib,sys
r=pathlib.Path(__file__).resolve().parent
m=r/'manifest.json'
assert hashlib.sha256(m.read_bytes()).hexdigest()==sys.argv[1], 'external anchor'
x=json.loads(m.read_text())
a={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p!=m}
assert a==set(x['files']), 'file inventory'
assert {str(p.relative_to(r)) for p in r.rglob('*') if p.is_dir()}==set(x['directories']), 'directory inventory'
for n,h in x['files'].items():
 p=r/n; assert not p.is_symlink(); assert hashlib.sha256(p.read_bytes()).hexdigest()==h,n
for e in json.loads((r/'source021-receipts.json').read_text()):
 b=(r/e['path']).read_bytes(); assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
print('PASS strict inventory, external anchor, source Git blobs')

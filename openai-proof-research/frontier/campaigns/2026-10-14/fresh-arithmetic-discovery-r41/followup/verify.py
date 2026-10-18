import pathlib,json,hashlib,sys
r=pathlib.Path(__file__).resolve().parent
m=r/'manifest.json'
assert hashlib.sha256(m.read_bytes()).hexdigest()==sys.argv[1], 'external anchor'
x=json.loads(m.read_text()); entries=list(r.rglob('*'))
assert all(not p.is_symlink() for p in entries), 'symlink'
assert {str(p.relative_to(r)) for p in entries if p.is_file() and p!=m}==set(x['files']), 'file inventory'
assert {str(p.relative_to(r)) for p in entries if p.is_dir()}==set(x['directories']), 'directory inventory'
for n,h in x['files'].items():assert hashlib.sha256((r/n).read_bytes()).hexdigest()==h,n
t=r/'context/preprints-tree.json'
assert hashlib.sha256(t.read_bytes()).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b', 'canonical tree'
tree=json.loads(t.read_text());assert tree['truncated']==False and len(tree['tree'])==13223
es={e['path']:e for e in tree['tree']}
inv=json.loads((r/'inventory.json').read_text())
for e in inv:assert es[e['path']]==e
receipts=json.loads((r/'receipts.json').read_text())
assert {e['path'][8:] for e in receipts}=={e['path'] for e in inv if not e['path'].endswith('.pdf')}, 'complete non-PDF inventory'
for e in receipts:
 b=(r/e['path']).read_bytes(); h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==e['git_blob']==es[e['path'][8:]]['sha']
print('PASS external anchor, strict inventory, canonical tree, all48 source blobs')

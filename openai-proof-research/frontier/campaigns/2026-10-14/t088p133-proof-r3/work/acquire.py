from pathlib import Path
import urllib.request,hashlib,json,tarfile,io
r=Path(__file__).resolve().parents[1]; repo=r.parents[3]
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
treefile=repo/'sources/preprints-tree.json'; tree=json.loads(treefile.read_text())
assert hashlib.sha256(treefile.read_bytes()).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
assert tree['truncated']==False and len(tree['tree'])==13223
entries={x['path']:x for x in tree['tree']}
base='preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/'
petty='preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/'
paths=[base+x for x in ['README.md','build/main.tex','build/references.tex']]+[petty+x for x in ['README.md','build/latex/main.tex','build/latex/sections/01_introduction.tex','build/latex/sections/06_conclusion.tex','build/latex/sections/07_consequences.tex']]
log=[]
for p in paths:
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{p}'
 body=urllib.request.urlopen(url,timeout=30).read(); meta=entries[p.removeprefix('preprints/') ] if p not in entries else entries[p]
 blob=hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()
 assert blob==meta['sha'] and len(body)==meta['size'],p
 dest=r/'packet/private/upstream'/p; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(body)
 log.append(dict(url=url,path=str(dest.relative_to(r)),sha256=hashlib.sha256(body).hexdigest(),git_blob=blob,tree_authenticated=True))
for suffix,name in [('e-print/2610.13953v1','fhlx-2610.13953v1-eprint.tar'),('pdf/2610.13953v1','fhlx-2610.13953v1.pdf')]:
 url='https://arxiv.org/'+suffix
 body=urllib.request.urlopen(url,timeout=30).read(); dest=r/'packet/private/primary'/name; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(body)
 old=repo/'frontier/campaigns/2026-10-14/t088p133-proof-r2/downloads'/name
 assert body==old.read_bytes(),name
 log.append(dict(url=url,path=str(dest.relative_to(r)),sha256=hashlib.sha256(body).hexdigest(),matches_r2=True))
 if name.endswith('.tar'):
  with tarfile.open(fileobj=io.BytesIO(body)) as tf:
   for member in tf.getmembers():
    assert Path(member.name).name==member.name
    if member.isfile():
     d=dest.parent/'fhlx-src'/member.name;d.parent.mkdir(exist_ok=True);d.write_bytes(tf.extractfile(member).read())
(r/'packet/private/acquisition.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))

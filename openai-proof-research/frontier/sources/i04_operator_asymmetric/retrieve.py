"""Retrieve only assigned research artifacts; immutable upstream URLs."""
import hashlib, json, urllib.request, concurrent.futures, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
inputs=['AGENTS.md','sources/upstream.json','frontier/iterations/README.md','frontier/iterations/i02-operator-r2.md','frontier/iterations/i03-operator-halfspace.md','frontier/reviews/i03-operator-halfspace-r4.md']
(OUT/'input_manifest.json').write_text(json.dumps([{'path':p,'sha256':hashlib.sha256((ROOT/p).read_bytes()).hexdigest()} for p in inputs],indent=2)+'\n')
old=json.loads((ROOT/'frontier/sources/i03_operator/upstream_manifest.json').read_text())
selected=[r for r in old if any(r['path'].endswith(s) for s in ['weights.tex','intertwiner.tex','introduction.tex','conclusion.tex','00-introduction.tex','product-structure.tex'])]
def fetch(r):
    data=urllib.request.urlopen(r['url'],timeout=45).read()
    sha=hashlib.sha256(data).hexdigest();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert sha==r['sha256'] and blob==r['git_blob_sha1']
    path=OUT/Path(r['file']).name;path.write_bytes(data)
    return dict(r,file=str(path.relative_to(ROOT)),sha256=sha,git_blob_sha1=blob,fresh_download_matches=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: rows=list(pool.map(fetch,selected))
(OUT/'upstream_manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
literature=[('teschl2000','https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf'),('kubrusly1997','https://jot.theta.ro/jot/archive/1997-038-002/1997-038-002-006.pdf'),('matache1994','https://lematematiche.dmi.unict.it/index.php/lematematiche/article/download/517/486')]
logs=[]
for name,url in literature:
    rec={'name':name,'url':url}
    try:
        data=urllib.request.urlopen(url,timeout=45).read();assert data.startswith(b'%PDF'), 'Not PDF'
        pdf=OUT/(name+'.pdf');pdf.write_bytes(data)
        subprocess.run(['pdftotext','-layout',str(pdf),str(OUT/(name+'.txt'))],check=True)
        rec.update(file=str(pdf.relative_to(ROOT)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),status='downloaded')
    except Exception as e: rec.update(status='failed',error=str(e))
    logs.append(rec)
(OUT/'literature_manifest.json').write_text(json.dumps(logs,indent=2)+'\n')
print(json.dumps({'upstream_files':len(rows),'literature':logs},indent=2))

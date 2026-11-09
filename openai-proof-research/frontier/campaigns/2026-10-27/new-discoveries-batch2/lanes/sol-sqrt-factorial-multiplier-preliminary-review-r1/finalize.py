from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
rows=json.loads((p/'freeze.json').read_text())
for r in rows:
    r['sha256_after_review']=hashlib.sha256(Path(r['original']).read_bytes()).hexdigest()
    r['copy_sha256_after_review']=hashlib.sha256(Path(r['copy']).read_bytes()).hexdigest()
    assert r['sha256_before']==r['sha256_after_freeze']==r['sha256_after_review']==r['copy_sha256_after_review']
(p/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
files={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest()
       for f in sorted(p.rglob('*')) if f.is_file() and f.name not in {'final-manifest.json','verification-receipt.json'}}
(p/'final-manifest.json').write_text(json.dumps({'algorithm':'sha256','excludes':['final-manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print('Manifest written:',len(files),'files; no self or receipt.')

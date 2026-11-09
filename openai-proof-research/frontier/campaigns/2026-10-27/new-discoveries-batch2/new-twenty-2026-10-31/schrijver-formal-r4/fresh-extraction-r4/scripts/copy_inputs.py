from pathlib import Path
import hashlib,json,shutil
lane=Path(__file__).resolve().parent.parent
base=lane.parent
files=['leads-review-r122/REVIEW.md','leads-review-r122/review.json','leads-review-r122/outputs/graph-27-12-certificate.json','leads-review-r122/outputs/graph-28-12-certificate.json','leads-review-r122/outputs/certificate-checks.json','expanded-corpus-r122/SCHRIJVER-NOTES.md','expanded-corpus-r122/sources/2112.01884v2.txt','expanded-corpus-r122/sources/2112.01884v2.pdf','r122-leads-root-ruling.json']
files += [str(p.relative_to(base)) for p in (base/'leads-review-r122/scripts').glob('*') if p.is_file()]
manifest={}
for rel in files:
 p=base/rel; data=p.read_bytes(); manifest[rel]=hashlib.sha256(data).hexdigest()
 q=lane/'inputs'/rel; q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
(lane/'outputs/input-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({r:len((base/r).read_bytes()) for r in files},indent=2))

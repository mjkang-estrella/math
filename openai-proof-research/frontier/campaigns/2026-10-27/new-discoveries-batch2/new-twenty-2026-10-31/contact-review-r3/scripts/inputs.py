from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[1]; b=r.parent
items=['contact-formal-r6/formal','contact-formal-r6/contact-r6-source.zip','contact-formal-r6/STATEMENT-CORRESPONDENCE.md','contact-formal-r6/REGRESSION.md','contact-formal-r6/SUMMARY.md','contact-formal-r6/results.json','contact-formal-r6/scripts','contact-formal-r6/fresh-extraction/replay-logs','contact-root-ruling-r2.json','contact-review-r2/REVIEW.md','contact-review-r2/review.json','contact-review-r2/scripts','contact-review-r1/REVIEW.md','contact-review-r1/review.json','contact-review-r1/SourceContactDefinition.lean','expanded-corpus-r117/outputs/contact-counterexample.md','contact-manuscript-r1/paper','contact-manuscript-r1/PROOF.md','contact-manuscript-r1/STATEMENT-CORRESPONDENCE.md']
items += [str(p.relative_to(b)) for p in (b/'expanded-corpus-r117/sources').glob('*') if p.name.startswith(('2410.10695.','bickel-hong.'))]
h={}
for item in items:
 p=b/item
 assert p.exists(),p
 for f in sorted(p.rglob('*')) if p.is_dir() else [p]:
  if f.is_file():h[str(f.relative_to(b))]=hashlib.sha256(f.read_bytes()).hexdigest()
(r/('inputs-'+sys.argv[1]+'.json')).write_text(json.dumps(h,indent=2)+'\n')
print(len(h),'hashes',hashlib.sha256(json.dumps(h,sort_keys=True).encode()).hexdigest())
if sys.argv[1]=='after':assert h==json.loads((r/'inputs-before.json').read_text())

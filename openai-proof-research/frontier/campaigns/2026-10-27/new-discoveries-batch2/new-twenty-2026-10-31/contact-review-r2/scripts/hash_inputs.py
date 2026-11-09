import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parents[2]
files=set((p/'contact-formal-r5/formal').glob('*'))
for lane, pats in {'contact-formal-r5':['statement-correspondence.md','STATEMENT-CORRESPONDENCE.md','SUMMARY.md'],'contact-manuscript-r1':['paper/*','PROOF.md','STATEMENT-CORRESPONDENCE.md','contact-source-only.zip','receipts/**/*','evidence/r5-fresh-replay/**/*'],'contact-review-r1':['REVIEW.md','review.json','SourceContactDefinition.lean'],'expanded-corpus-r117':['sources/2410.10695.*','sources/bickel-hong*','outputs/contact-counterexample.md']}.items():
 for pat in pats: files.update((p/lane).glob(pat))
print(json.dumps({str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(files) if f.is_file()},indent=2))

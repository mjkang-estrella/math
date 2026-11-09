from pathlib import Path
import hashlib,json,shutil
D=Path(__file__).resolve().parents[1]; P=D.parent
files=[]
def add(p):
 if p.is_file(): files.append(p)
def tree(p):
 for f in p.rglob('*'):
  if f.is_file() and f.suffix not in ['.olean','.ilean','.pyc']:add(f)
R=P/'kirchhoff-formal-r2'
for n in ['formal','receipts','negative','scripts']:tree(R/n)
for n in ['kirchhoff-source-only.zip','SUMMARY.md','statement-correspondence.md','results.json','replay.py','REPRODUCE.md']:add(R/n)
for n in ['review.json','REVIEW.md']:add(P/'kirchhoff-review-r1'/n)
for n in ['outputs','receipts','scripts']:tree(P/'kirchhoff-review-r1'/n)
for n in ['ReviewerControls.lean','ReviewerRestatement.lean']:add(P/'kirchhoff-review-r1/fresh/formal'/n)
for n in ['PRIOR-ART.md','exact-independent.json']:add(P/'kirchhoff-formal-r1'/n)
# exact-independent can be under outputs
for f in (P/'kirchhoff-formal-r1').rglob('exact-independent.json'):add(f)
for n in ['kirchhoff-root-ruling-r1.json','kirchhoff-root-adjudication-r2.json']:add(P/n)
tree(P/'kirchhoff-parent-prior-art')
C=P/'expanded-corpus-r105'
add(C/'KIRCHHOFF-LEAD.md');add(C/'raw/349441.jsonl')
for f in (C/'sources').glob('2101.07103.*'):add(f)
files=sorted(set(files)); H={str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
(D/'input-hashes-before.json').write_text(json.dumps(H,indent=2)+'\n')
assert H['kirchhoff-formal-r2/kirchhoff-source-only.zip']=='927d6c3cb8977308a190122f511788bd8606a7cdcbf28ccbc159852b8830ea3c'
for f in files:
 dst=D/'sources'/f.relative_to(P);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
for f in (R/'formal').glob('*.lean'):shutil.copyfile(f,D/'formal'/f.name)
for f in (R/'negative').glob('*.lean'):shutil.copyfile(f,D/'negative'/f.name)
shutil.copyfile(P/'kirchhoff-review-r1/fresh/formal/ReviewerControls.lean',D/'checks/ReviewerControls.lean')
shutil.copyfile(R/'replay.py',D/'replay.py');shutil.copyfile(R/'scripts/run.py',D/'scripts/run.py')
shutil.copyfile(R/'statement-correspondence.md',D/'statement-correspondence.md')
print('Bound and copied',len(H),'files')

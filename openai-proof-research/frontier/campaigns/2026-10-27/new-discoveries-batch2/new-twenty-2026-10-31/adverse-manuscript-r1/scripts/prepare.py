from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parents[1]; P=R.parent
paths=[]
for name in ['adverse-formal-r2','adverse-review-r1','adverse-formal-r1']:
 paths += [p for p in (P/name).rglob('*') if p.is_file()]
paths += [P/n for n in ['adverse-root-ruling-r1.json','adverse-root-adjudication-r2.json']]
E=P/'expanded-corpus-r101'
paths += [E/n for n in ['outputs/LATIN36-ORDINARY-PROOF.md','outputs/latin36-certificate.json','raw/381433.jsonl','sources/381433.pdf','sources/381433.txt']]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
b={str(p.relative_to(P)):h(p) for p in sorted(set(paths))}
(R/'receipts/frozen-before.json').write_text(json.dumps(b,indent=2)+'\n')
assert h(P/'adverse-formal-r2/adverse-381433-source.zip')=='aefc4cc7ea17aa2ae0797a739ee8ec40b56097c281e0435f403c4e93de47420b'
def cp(p,q):
 q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert h(p)==h(q)
for p in (P/'adverse-formal-r2/formal').glob('*.lean'):cp(p,R/'formal'/p.name)
cp(P/'adverse-review-r1/extracted/formal/Reviewer.lean',R/'formal/Reviewer.lean')
for n in ['replay.py','scripts/bounded.py','scripts/lean.sh','scripts/checker.sh','scripts/check_exact.py']:
 p=P/'adverse-formal-r2'/n
 if p.exists():cp(p,R/n)
for lane,names in {
'adverse-formal-r2':['PROOF.md','STATEMENT-CORRESPONDENCE.md','results.json','SOURCE-MANIFEST.json','adverse-381433-source.zip'],
'adverse-review-r1':['REVIEW.md','review.json'],
'adverse-formal-r1':['PRIOR-ART.md','PRIOR-ART.json']}.items():
 for n in names:
  p=P/lane/n
  if p.exists():cp(p,R/'inputs'/lane/n)
 for p in (P/lane/'receipts').glob('*'):
  if p.is_file():cp(p,R/'inputs'/lane/'receipts'/p.name)
for p in (P/'adverse-formal-r1/sources').glob('*'):
 if p.is_file() and not p.name.startswith(('omega-','openai-')):cp(p,R/'inputs/sources'/p.name)
for n in ['euro2012.pdf','euro2012.txt']:cp(P/'adverse-review-r1/sources'/n,R/'inputs/sources'/n)
for n in ['adverse-root-ruling-r1.json','adverse-root-adjudication-r2.json']:cp(P/n,R/'inputs'/n)
for n in ['outputs/LATIN36-ORDINARY-PROOF.md','outputs/latin36-certificate.json','raw/381433.jsonl','sources/381433.pdf','sources/381433.txt']:cp(E/n,R/'inputs'/n)
cp(P/'adverse-formal-r2/PROOF.md',R/'PROOF.md');cp(P/'adverse-formal-r2/STATEMENT-CORRESPONDENCE.md',R/'STATEMENT-CORRESPONDENCE.md')
print('Bound',len(b),'files; copied sources with hash identity')

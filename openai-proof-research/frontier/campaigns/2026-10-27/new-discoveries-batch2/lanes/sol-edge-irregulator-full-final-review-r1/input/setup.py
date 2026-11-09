from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent; P=L/'packet'; P.mkdir(); (P/'formal').mkdir();(P/'evidence').mkdir();(P/'logs').mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for comp in ['lower','upper']:
 for n,h in json.loads((L/comp/'manifest.json').read_text()).items():assert sha(L/comp/n)==h,(comp,n)
for f in (L/'lower/formal').glob('*.lean'):
 if f.stem not in ['OriginAudit','AuditPrint']:shutil.copyfile(f,P/'formal'/f.name)
for f in (L/'upper/formal').glob('*.lean'):
 if f.stem in ['OriginAudit','AuditPrint']:continue
 dest=P/'formal'/f.name
 if dest.exists():assert dest.read_bytes()==f.read_bytes()
 else:shutil.copyfile(f,dest)
for f in ['pins.json','dependency-hashes.json','guard.py']:shutil.copyfile(L/'upper'/f,P/f)
shutil.copyfile(L/'helper_guard.py',P/'helper_guard.py')
# Union package dependency hashes, rejecting contradictory entries.
d={}
for comp in ['lower','upper']:
 for row in json.loads((L/comp/'dependency-hashes.json').read_text()):
  if row['path'] in d:assert d[row['path']]==row
  d[row['path']]=row
(P/'dependency-hashes.json').write_text(json.dumps(list(d.values()),indent=2)+'\n')
for lane,files in {'sol-edge-irregulator-lower-source-formal-r2':['SUMMARY.md','FAILURES.md','fresh-replay.log'], 'sol-edge-irregulator-upper-formal-r2':['SUMMARY.md','fresh-replay.log'], 'sol-edge-irregulator-preliminary-review-r1':['review.md'], 'sol-edge-irregulator-current-prior-review-r2':['review.md'], 'root-edge-irregulator-formal-investment-r1':['ADOPTION.json'], 'root-edge-irregulator-source-replay-r2':['ADOPTION.json'], 'sol-fresh-source-discovery-r70':['PROOF.md']}.items():
 for f in files:
  dst=P/'evidence'/lane/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(B/'lanes'/lane/f,dst)
for comp in ['lower','upper']:
 for folder in ['failures','probes']:
  if (L/comp/folder).exists():shutil.copytree(L/comp/folder,P/'evidence'/comp/folder)
for f in ['AGENTS.md','ledger.json','prior-campaign-context.json','NEXT.md']:shutil.copyfile(B/f,P/'evidence'/f)
shutil.copyfile(B.parents[3]/'AGENTS.md',P/'evidence/ancestor-AGENTS.md')
shutil.copyfile(B/'lanes/sol-edge-irregulator-current-prior-review-r2/live/publisher.pdf',P/'evidence/publisher.pdf')
print('union',sorted(p.stem for p in (P/'formal').glob('*.lean')),'dependency hashes',len(d))

from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-pendulum-time-map-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for freeze in [P/'review-freeze.json',P.parent/'root-r166-preliminary-freeze-r1/review-freeze.json']:
 for r in json.loads(freeze.read_text())['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
l=json.loads((B/'ledger.json').read_text());assert l['accepted_count']==9 and l['total_accepted_count']==39
intro='''Pendulum ordinary proof PASS adopted with independent endpoint supplement:
literal Conjecture1 holds on z in[0,2], every0<phi<pi/2. Additional branch
expectations remain outside scope. Root independent-checker replay is byte
identical;57 candidate originals/96 review payload entries verified;
100 review files frozen. Publication history and classical subsumption HOLD.
Focused Sol source/subsumption review assigned; no Lean/paper investment.
See root-pendulum-preliminary-adoption-r1. Steiner source/prior review and
Sol r168 research continue. Counts9 additional/39 total,next40;credit0.

'''
n=(B/'NEXT.md').read_text();heading='# Current continuation — 29 October 2026\n'
assert intro not in n and heading in n
(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(x) for x in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Adopt pendulum endpoint proof review and retain source holds','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

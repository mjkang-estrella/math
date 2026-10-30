from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
S=P.parent/'sol-kazemi-hypercube-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
for row in json.loads((S/'provenance.json').read_text())['evidence_files']:
 p=Path(row['path']);assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
intro='''Kazemi hypercube Conjecture 6.1: root adopts routine-source-bridge exclusion
after independent ordinary mathematics PASS. The weighted capacity bound,
active representatives and strict inactive equality case close the full scope;
this is not a claim of an earlier published proof. Root reproduces the independent
checks and verifies 34 candidate / 45 review evidence paths before and after.
See root-kazemi-hypercube-exclusion-r1/DECISION.md; novelty limits remain explicit.
No Lean or paper investment. Sol r156 replaces the review; r154 and r155 continue.
Counts remain 9 additional / 39 total; next 40.

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
subprocess.run(git+['commit','-m','Adjudicate Kazemi proof as uncredited source adaptation','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

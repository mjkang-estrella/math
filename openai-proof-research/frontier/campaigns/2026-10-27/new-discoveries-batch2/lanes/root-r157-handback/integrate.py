from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r157'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for name in ['finalmanifest.json','scientific-freeze.json']:
 for r in json.loads((S/name).read_text())['files']:
  p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
intro='''r157 general-H entropy-bound conjecture remains unresolved. The scalar
first variation defeats a lower-bound shortcut but supplies no admissible metric
or entropy counterexample. Curvature CM, mass dependence and normalization gaps
remain. Root verifies 53 manifest / 52 freeze paths and replays 40 variation,
303 rational and four symbolic controls. See root-r157-handback.
Sol r160 replaces r157; r158 and r159 continue. Counts remain 9 additional /
39 total, next 40. New uncapped registry deltas do not close old capped gaps.

'''
n=(B/'NEXT.md').read_text();heading='# Current continuation — 29 October 2026\n';assert intro not in n and heading in n
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
subprocess.run(git+['commit','-m','Record unresolved entropy bound and scalar method obstruction','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
sources=[P.parent/f'sol-fresh-source-discovery-r{n}' for n in [131,132]]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
for S in sources:
 for r in json.loads((S/'finalmanifest.json').read_text())['files']:assert sha(S/r['path'])==r['sha256']
intro='''r131/r132 adopted zero nominees. Total isolation/tree bounds and arbitrary-field
SK worst-start mixing remain unresolved. Root verifies 89/82 manifest entries,
replays 288 sampled minimax graphs, five component controls, and SK route
obstructions. These are not universal bounds or source counterexamples.
Public weighted-bond, cubic synchronization and Kikuchi exclusions and all
scope qualifications remain preserved. See root-r131-r132-handback.
Counts stay 9 additional / 39 total. Sol r135/r136 replace completed slots;
r134 continues. New briefs reuse qualified history indexes with changed-record
coverage rather than repeating unchanged inventories.

'''
n=(B/'NEXT.md').read_text();assert 'r131/r132 adopted zero nominees.' not in n
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P]+sources:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record isolation-game and arbitrary-field SK gaps without credit','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

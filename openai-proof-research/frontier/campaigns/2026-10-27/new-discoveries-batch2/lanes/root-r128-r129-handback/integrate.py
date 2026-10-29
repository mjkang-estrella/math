from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
sources=[P.parent/f'sol-fresh-source-discovery-r{n}' for n in [128,129,130]]
for n,S in zip([128,129,130],sources):
 raw=json.loads((S/('manifest.json' if n==129 else 'finalmanifest.json')).read_text())
 m=raw if n==129 else raw['entries' if n==128 else 'files']
 for r in m:assert sha(S/r['path'])==r['sha256']
intro='''r128/r129/r130 adopted zero nominees. Spectral saturation is public; domino
quotient positivity and even-cycle lower bounds remain unproved. All three r129
questions are old (Radon r47/r34 and unimodular Jensen r52). The r130 Galois,
Ulam and ultrafilter questions remain unresolved. Root verifies 67/66/157
manifest entries, replays twelve known constructions and short Ulam recursion;
r129 receives documentary checks only. See root-r128-r129-handback decisions.
Counts stay 9 additional / 39 total. Sol r131/r132/r133 replace completed slots,
with lightweight original-report duplicate screening required before retrieval.

'''
n=(B/'NEXT.md').read_text();assert 'r128/r129/r130 adopted zero nominees.' not in n
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
subprocess.run(git+['commit','-m','Record r128-r130 zero nominees and preserved unresolved scopes','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

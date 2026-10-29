from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
sources=[P.parent/f'sol-fresh-source-discovery-r{n}' for n in [126,127]]
for S in sources:
 raw=json.loads((S/'finalmanifest.json').read_text())['files']
 m=raw if isinstance(raw,dict) else {r['path']:r['sha256'] for r in raw}
 for p,h in m.items():assert sha(S/p)==h,p
intro='''r126/r127 adopted zero nominees. Wallis remainder, Szabó cutoff and centered
residue progression leads have public proofs; the Gaussian quotient implication
has a public refutation, leaving its broader classification unproved. Ferreira
Volterra source access remains incomplete. Root verifies 66/54 manifest entries
and replays 39 rational identities, 20 residue maxima and the exact quotient
witness in separate copies. See root-r126-r127-handback. Counts unchanged 9/39.
Sol r129/r130 replace the completed assignments; r128 continues.

'''
n=(B/'NEXT.md').read_text();assert 'r126/r127 adopted zero nominees.' not in n
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
subprocess.run(git+['commit','-m','Record r126 and r127 public exclusions and verified diagnostics','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

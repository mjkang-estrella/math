from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r158'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for name in ['finalmanifest.json','scientific-freeze.json']:
 for f,h in json.loads((S/name).read_text())['files'].items():assert sha(S/f)==h,f
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
intro='''r158 normalized integral Macdonald elementary positivity (Haglund–Kim–Oh–Yoo
2610.34772 Conjecture 1.1) remains unresolved. Root reproduces 132 functions,
132 source e_n controls, 29 orthogonal-definition comparisons and both method
obstructions; four outputs match byte-identically. Freeze: 46 manifest / 34
scientific entries. Generic Schur positivity and unchanged hook ribbons do not
supply the missing all-shape transform positivity. See root-r158-handback.
Sol r161 replaces r158; r159 and r160 continue. Counts unchanged: 9/39, next40.

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
subprocess.run(git+['commit','-m','Record unresolved Macdonald positivity and exact method controls','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

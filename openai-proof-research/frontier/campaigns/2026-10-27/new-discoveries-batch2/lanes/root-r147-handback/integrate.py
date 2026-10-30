from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r147'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for name in ['finalmanifest.json','scientific-freeze.json']:
 for r in json.loads((S/name).read_text())['files']:assert sha(S/r['path'])==r['sha256'],r['path']
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
intro='''r147 Kiro–Nishry critical prefactor-one polynomial infinitude remains
unresolved. Root verifies 36 manifest/32 scientific entries and independently
checks all 21 explicit polynomials through degree 20: 13,525 exact prefix
comparisons and 42 integer-cleared tail inequalities. These establish each
individual all-n bound, not unbounded degrees. The circle-supremum obstruction
does not exclude coefficient cancellation. See root-r147-handback. Sol r150
replaces r147; r148/r149 continue. Counts remain 9 additional / 39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r147 Kiro–Nishry critical prefactor-one' not in n
heading='# Current continuation — 29 October 2026\n';assert heading in n
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
subprocess.run(git+['commit','-m','Record unresolved critical polynomial infinitude and exact controls','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

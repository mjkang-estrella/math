from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r149'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for name in ['finalmanifest.json','scientific-freeze.json']:
 for r in json.loads((S/name).read_text())['files']:assert sha(S/r['path'])==r['sha256'],r['path']
assert json.loads((P/'replay-receipt.json').read_text())['status']=='PASS'
intro='''r149 Kaneko's full leaf-distance conjecture remains unresolved. Root
verifies 359 manifest/33 scientific entries and reproduces 524,287 deletion
sets, six windmill controls and 220 star exchanges. The family demonstrates
why bounded-leaf and strict one-edge-improvement shortcuts are insufficient;
it satisfies the source conclusion. Original-source/2017 body and registry
gaps remain. See root-r149-handback. Sol r152 replaces r149; r150/r151 continue.
Counts remain 9 additional / 39 total.

'''
n=(B/'NEXT.md').read_text();assert "r149 Kaneko's full leaf-distance conjecture remains unresolved." not in n
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
subprocess.run(git+['commit','-m','Record unresolved leaf-distance conjecture and route obstructions','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

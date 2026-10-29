from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r140'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for p,r in json.loads((S/'finalmanifest.json').read_text())['files'].items():assert sha(S/p)==r['sha256'],p
assert json.loads((P/'exact-replay.json').read_text())['exact']==json.loads((S/'checks.json').read_text())['exact']
(P/'replay-receipt.json').write_text(json.dumps({'status':'PASS','copied_exact_checker_section':True,'exact_records':20,'floating_search_not_repeated':True,'credit':0},indent=2)+'\n')
intro='''r140 Bellec–Fritz iid inequality remains unresolved: the universal
quartic upper bound is missing. Root verifies 56 manifest/54 scientific
entries and reproduces all20 exact records; no repeated floating search or
universal inference. Empirical-law and dyadic reductions are retained with
source/access/registry limits. See root-r140-handback. Sol r143 replaces
r140; r141/r142 continue. No credit; counts remain9 additional/39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r140 Bellec–Fritz iid inequality remains' not in n
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record unresolved iid quartic bound and exact dyadic controls','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

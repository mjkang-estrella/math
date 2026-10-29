from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r139'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for p,r in json.loads((S/'finalmanifest.json').read_text())['entries'].items():assert sha(S/p)==r['sha256'],p
assert sha(P/'replay/check-results.json')==sha(S/'check-results.json')
(P/'ADOPTION.json').write_text(json.dumps({'ordinary_math':'PASS, root independently checked','substantive':'EXCLUDE_ROUTINE_CORONA','prior_exact_refutation':'not asserted','copied_checker_replay':'PASS, byte-identical','manifest_entries':47,'credit':0,'additional':9,'total':39},indent=2)+'\n')
intro='''r139 Achour degree-spread conjecture is refuted by the 12-vertex
P6 corona, but root adopts routine-classical exclusion after reading the old
corona theorem and checking the complete private-leaf/matching reduction.
All 47 manifest/30 scientific entries verify; eight exact controls reproduce.
Wild-number source has verified large-order public overlap only; no full
public-refutation claim is adopted. See root-r139-handback. Sol r142 replaces
r139; r140/r141 continue. Credit0; accepted counts remain9/39.

'''
n=(B/'NEXT.md').read_text();assert 'r139 Achour degree-spread conjecture is refuted' not in n
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
subprocess.run(git+['commit','-m','Exclude degree-spread refutation via classical corona formula','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

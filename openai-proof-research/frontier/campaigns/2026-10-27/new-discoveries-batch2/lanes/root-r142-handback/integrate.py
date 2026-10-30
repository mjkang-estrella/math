from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];T=P.parent/'root-r143-handback'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
bases=[P,T]
for k in [142,143]:
 S=P.parent/f'sol-fresh-source-discovery-r{k}';bases.append(S)
 d=json.loads((S/'finalmanifest.json').read_text());rows=d.get('files',d.get('entries'))
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
assert sha(P/'replay/check-results.json')==sha(P.parent/'sol-fresh-source-discovery-r142/check-results.json')
for n in ['checks.json','geometry-checks.json']:assert sha(T/'replay'/n)==sha(P.parent/'sol-fresh-source-discovery-r143'/n)
(P/'replay-receipt.json').write_text(json.dumps({'status':'PASS','equivalent_upper_sum_check':True,'candidate_checker_defect':False,'root_initial_misinterpretation_corrected':True,'byte_identical_results':True,'manifest':25,'credit':0},indent=2)+'\n')
(T/'replay-receipt.json').write_text(json.dumps({'status':'PASS','copied_implementation_replay':True,'byte_identical_outputs':['checks.json','geometry-checks.json'],'manifest':59,'credit':0},indent=2)+'\n')
intro='''r142 Laplacian product/equality conjecture and r143 theta-convolution
optimal interval remain unresolved. Root verifies25 and59 manifest entries
and reproduces exact checks. Root's initial claim of a sum-check error was
incorrect: lower and upper forms are equivalent by complement/index reversal;
both pass. Scalar zero-endpoint profiles do not settle geometric realizability,
and the truncation shape derivative remains heuristic. See root-r142-handback
and root-r143-handback. Sol r145/r146 replace them; r144 continues.
No credit; counts remain9 additional/39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r142 Laplacian product/equality conjecture and r143' not in n
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in bases:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record unresolved Laplacian product and convolution interval gaps','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

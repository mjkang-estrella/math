from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];T=P.parent/'root-r146-handback'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
bases=[P,T]
for k,R in [(145,P),(146,T)]:
 S=P.parent/f'sol-fresh-source-discovery-r{k}';bases.append(S);counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['files']
  for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
  counts[name]=len(rows)
 names=['check-results.json','structure-results.json'] if k==145 else ['checks.json']
 for name in names:
  a=json.loads((S/name).read_text());b=json.loads((R/'replay'/name).read_text())
  if k==145 and name=='check-results.json':a.pop('seconds');b.pop('seconds')
  assert a==b,(k,name)
 (R/'replay-receipt.json').write_text(json.dumps({'status':'PASS','hash_counts':counts,'copied_implementation_replay':True,'equal_outputs':names,'ignored_nondeterministic_field':'check-results.seconds' if k==145 else None,'universal_proof_certified':False,'credit':0},indent=2)+'\n')
intro='''r145 Paone–Paone line-graph signature bound remains unresolved;
root verifies 66 manifest/37 scientific entries and reproduces 2,000 sampled
graphs and 4,980 attachment checks. The singular attachment diagnostic is
not a source counterexample. r146 Firey equality is excluded by the exact
earlier Kitamura public proof; 57 manifest/33 scientific entries verify and
168 exact controls reproduce. No root audit of all public Lean dependencies
is claimed. See root-r145-handback and root-r146-handback. Sol r149/r148
replace them; r147 continues. Counts remain 9 additional / 39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r145 Paone–Paone line-graph signature bound remains unresolved;' not in n
heading='# Current continuation — 29 October 2026\n';assert heading in n
(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in bases:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(x) for x in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record signature gap and prior Firey equality resolution','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

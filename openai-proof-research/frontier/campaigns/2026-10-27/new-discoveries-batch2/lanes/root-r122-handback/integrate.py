from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r122'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())
for k,v in m.items():assert sha(S/k)==v['sha256'] and (S/k).stat().st_size==v['bytes'],k
sl=json.loads((S/'source-lock.json').read_text())['files']
for r in sl:assert sha(S/r['path'])==r['sha256'],r['path']
shutil.copy2(S/'checks.py',P/'copied-checks.py')
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr)
j=json.loads((P/'check-results.json').read_text())
assert sum(r['graphs'] for r in j['exhaustive'])==2671
assert sum(r['graphs'] for r in j['random'])==219
assert j['failed_route_witnesses']['strict_local_descent']['global_optimum']==2
for k,v in m.items():assert sha(S/k)==v['sha256'],k
out={'status':'PASS','manifest_entries':len(m),'scientific_source_hashes':len(sl),'copied_checker_sha256':sha(P/'copied-checks.py'),'exhaustive_graphs':2671,'eligible_random_samples':219,'credit':0,'counts':[9,39],'qualification':'Copied worker checker replay. Formula checked independently in prose; finite tests establish no uniform n/6 inequality. Whole-lane historical exclusions retain a source-screen gap.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text()
intro='''r122 TI-augmentation Conjecture6.1/7.4 remains unresolved. Root verifies49
manifest entries/seven scientific hashes and replays2671 exhaustive comparisons,
219 weak random samples, and three method obstructions. Fixed-I cost formula
does not establish the universal n/6 bound. Whole r111–r113 historical exclusions
omit scientific reports; no freshness clearance adopted. See root-r122-handback.
Sol r125 replaces r122, instructed to skip generated caches rather than entire
lanes. Fresh r123/r124 continue; counts unchanged9additional/39total.

'''
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
subprocess.run(git+['commit','-m','Record unresolved TI augmentation and exact route obstructions','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(out))

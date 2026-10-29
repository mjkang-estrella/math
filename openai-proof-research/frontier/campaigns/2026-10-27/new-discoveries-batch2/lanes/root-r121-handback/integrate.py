from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r121'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
for k,v in m.items():assert sha(S/k)==v['sha256'] and (S/k).stat().st_size==v['bytes'],k
shutil.copy2(S/'checks.py',P/'copied-checks.py')
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr)
j=json.loads((P/'check-results.json').read_text())
assert len(j['root_inequalities'])==72 and all(x['strict'] for x in j['root_inequalities'])
assert j['motzkin_independent_recurrence_agreements']==82
assert j['published_coarse_envelope_failure']['HouLi_multiplicative_bound_greater_than_one']
for k,v in m.items():assert sha(S/k)==v['sha256'],k
out={'status':'PASS','manifest_entries':len(m),'copied_checker_sha256':sha(P/'copied-checks.py'),'finite_root_centers':72,'recurrence_agreements':82,'credit':0,'counts':[9,39],'qualification':'Copied worker checker replay; no all-order proof or new independent implementation.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text()
intro='''r121 adopted zero nominees: crown/polygon and W2 questions have public proofs;
Zhao alternating-Motzkin root concavity is an old r87 screen, still incomplete.
Root verifies66 manifest entries and replays72 finite inequalities/two recurrence
constructions. Method obstructions are not source counterexamples. New Sol r124
must perform an uncapped target-specific duplicate pass before sustained work.
Fresh r122/r123 continue; counts unchanged9additional/39total. Root record:
lanes/root-r121-handback/DECISION.md and ADOPTION.json.

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
subprocess.run(git+['commit','-m','Record r121 public exclusions and old unresolved Zhao question','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(out))

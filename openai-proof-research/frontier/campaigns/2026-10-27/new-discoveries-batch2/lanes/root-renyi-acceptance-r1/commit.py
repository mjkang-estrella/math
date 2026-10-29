from pathlib import Path
import json,hashlib,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
old=json.loads(subprocess.check_output(git+['show','HEAD:'+str((B/'ledger.json').relative_to(repo))],cwd=repo))
new=json.loads((B/'ledger.json').read_text())
assert old['accepted_count']==8 and new['accepted_count']==9
assert new['accepted'][:-1]==old['accepted'] and new['excluded'][:-1]==old['excluded']
assert new['total_accepted_count']==39 and new['next_global_outcome_number']==40
assert new['accepted'][-1]['number']==39 and new['accepted'][-1]['discovery_count_credit']==1
paths=[B/'ledger.json',B/'NEXT.md',B/'RESULTS.md',B/'candidate-packets/subunit-renyi-threshold-refutation.zip']
bulk=[]
for base in [P,B/'candidates/renyi-threshold',P.parent/'root-factorial-final-exclusion-r1',P.parent/'sol-factorial-product-full-final-review-r1',P.parent/'sol-renyi-final-delta-closure-r4']:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or any(p.name.endswith(s) for s in ['.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so']):continue
  if p.stat().st_size>10*1024*1024:
   h=hashlib.sha256()
   with p.open('rb') as f:
    for c in iter(lambda:f.read(1048576),b''):h.update(c)
   bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':h.hexdigest()})
  else:paths.append(p)
out=P/'unstaged-bulk-evidence.json';out.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(out)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Accept Renyi threshold refutation as outcome39; exclude routine factorial collision','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

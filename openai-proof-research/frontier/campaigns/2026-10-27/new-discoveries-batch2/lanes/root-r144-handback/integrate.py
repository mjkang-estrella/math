from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
S=P.parent/'sol-fresh-source-discovery-r144'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((S/'finalmanifest.json').read_text())['files']
for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
a=json.loads((S/'checks.json').read_text());b=json.loads((P/'replay/checks.json').read_text())
a.pop('utc');b.pop('utc');assert a==b
receipt={'status':'PASS','manifest':len(rows),'copied_implementation_replay':True,'equal_except_utc':True,'tested_states':b['tested_states'],'truncation_checks':b['truncation_checks'],'independent_compositions':b['independent_compositions'],'count_comparisons':len(b['independent_counts']),'universal_proof':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
intro='''r144 fixed-multiplicity infinite-chain quasipolynomiality remains
unresolved. Root verifies all 75 manifest entries and reproduces 11,340 states,
2,861 quotient checks, 9,907 compositions and 77 count comparisons (only the
execution timestamp differs). The earlier overlapping public abstract is
recorded with its unread 403-blocked proof body; no verified prior-proof claim
is adopted. See root-r144-handback. Sol r147 replaces r144; r145/r146 continue.
No credit; counts remain 9 additional / 39 total.

'''
n=(B/'NEXT.md').read_text();assert 'r144 fixed-multiplicity infinite-chain' not in n
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
subprocess.run(git+['commit','-m','Record unresolved semigroup count and unread public overlap','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(receipt))

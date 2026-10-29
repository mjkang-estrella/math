from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r141'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for r in json.loads((S/'finalmanifest.json').read_text())['files']:assert sha(S/r['path'])==r['sha256'],r['path']
assert sha(P/'replay/checks.json')==sha(S/'checks.json')
(P/'replay-receipt.json').write_text(json.dumps({'status':'PASS','copied_checker_replay':True,'byte_identical_results':True,'identity_pairs':65536,'large_prime_pairs':52,'lcm_cross_checks':9,'credit':0},indent=2)+'\n')
intro='''r141 Entin–Landsberg function-field LCM remains unresolved. Root
verifies91 manifest entries and reproduces 65,536 polynomial identities,
52 large-prime collision pairs and9 LCM cross-checks. The constant-per-shift
resultant bound is only O(q^n), not the needed o(q^n); the finite collision
is a method obstruction. Both registry intervals remain capped. A root
manifest-schema error was corrected and preserved. See root-r141-handback.
Sol r144 replaces r141; r142/r143 continue. Credit0; counts9/39.

'''
n=(B/'NEXT.md').read_text();assert 'r141 Entin–Landsberg function-field LCM remains' not in n
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
subprocess.run(git+['commit','-m','Record unresolved function-field LCM collision estimate','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

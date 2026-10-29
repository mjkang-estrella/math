from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];V=P.parent/'sol-frank-attenuation-preliminary-review-r1';S=P.parent/'sol-fresh-source-discovery-r136'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for r in json.loads((V/'manifest.json').read_text())['files']:assert sha(V/r['path'])==r['sha256']
for r in json.loads((P.parent/'root-frank-attenuation-preliminary-freeze-r1/review-freeze.json').read_text())['files']:assert sha(S/r['path'])==r['sha256']
assert sha(P/'replay/independent-check.json')==sha(V/'independent-check.json')
(P/'ADOPTION.json').write_text(json.dumps({'source':'PASS','ordinary_math':'PASS','substantive':'EXCLUDE_ROUTINE_ADAPTATION','prior_explicit_frank_resolution':'not established','candidate_unchanged':59,'review_unchanged':74,'independent_checker_replay':'PASS, byte-identical','credit':0,'additional':9,'total':39,'decision':'DECISION.md'},indent=2)+'\n')
intro='''Frank ordinal attenuation is EXCLUDED from discovery credit after root
adopts the independent complete one-sided conditional-regression/first-variation
and monotone quantization bridge. Source and ordinary mathematics pass; both
exact finite certificates pass. Beare/Student-t body gaps remain explicit and
no earlier exact Frank refutation is asserted. No Lean or manuscript investment.
See root-frank-attenuation-exclusion-r1. Counts unchanged9/39. Sol r140
replaces the completed review; r138/r139 continue fresh research.

'''
n=(B/'NEXT.md').read_text();assert 'Frank ordinal attenuation is EXCLUDED' not in n
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,V]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Exclude Frank attenuation as complete classical variational adaptation','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)

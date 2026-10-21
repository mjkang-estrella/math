from pathlib import Path
import fnmatch,json,os
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r165'
G=json.loads((OWN/'tools/guards.json').read_text())
def blocked(path):
 s=str(path).replace('\\','/').casefold()
 parts=s.split('/')
 if any(x in G['exact_components'] for x in parts): return 'dependency'
 if any(fnmatch.fnmatchcase(s,p) for p in G['patterns']): return 'explicit'
 if any(c in part for part in parts for c in G['coarse']): return 'coarse'
 return None
def check():
 paths=['campaigns/X-ANALYTIC-R159-brief.md','campaigns/x-arithmetic-r132-proof.md','x/y/structural-r161-author/a.md','x-t126s161.md','x-t360s147.md','x/STRUCTURAL-r164/a.md','x/outsideREPORTopaque.md','x/FINALdata/x','x/inputs/foo','x/sources/foo','x/snapshots/foo','x/ledgers/foo','x/metadata/a','x/R165-dispatch.md','x/capture.md','x/retrievalfoo/a','x/retrievefoo/a','x/diagnostic.md','x/stdout.md','x/stderr.md','x/reproduction.md','x/resume.md','x/launch.md','x/scout.md','x/tasks.json','x/TEN-FINDINGS.md','x/twenty-findings.md','x/second-history-screen/a','x/history-screen.md','x/history-broad-geometry.md','x/prepare.py','x/NEW-TEN.md','x/terminal-summary','x/summary.json','x/.git/a','x/dependencies/a','x/fresh-structural-discovery-r165/notes/a']
 assert all(blocked(x) for x in paths)
 assert blocked('frontier/campaigns/2026-10-14/structural-r140/notes/mathematics.md') is None
 return {'synthetic_only':True,'protected_examples':len(paths),'all_protected_examples_pruned':True,'opaque_aliases':'unrecognizable aliases cannot be certified absent','coarse_omissions':'substring guards intentionally omit some potentially relevant authored material'}
def walk():
 # No symlink following; directory predicates run before descent, file predicates before read.
 for cur,ds,fs in os.walk(ROOT,topdown=True,followlinks=False):
  rel=Path(cur).relative_to(ROOT)
  ds[:]=sorted(d for d in ds if not blocked(rel/d) and not (Path(cur)/d).is_symlink())
  for name in sorted(fs):
   rp=rel/name
   if not blocked(rp) and not (ROOT/rp).is_symlink(): yield rp
if __name__=='__main__': print(json.dumps(check(),indent=2))

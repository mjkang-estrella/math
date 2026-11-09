"""Bounded local history search; prunes directories before descent and filenames before reading."""
from pathlib import Path
import os, re, json, hashlib, fnmatch
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
active=['*analytic*r138*','*structural*r144*','*analytic*r137*','t177c143-*','*structural*r143*','t373e135-*','*analytic*r135*','*analytic*r136*','k369r134-*','t088p133-*','*arithmetic*r108*']
coarse=re.compile(r'(^|[-_.])(private|inputs?|snapshots?|frozen|copies|copy|corpus|fixtures?|controls?|sources?|renders?|vendor|archives?|inventor(?:y|ies)|outside|release|publication|reviews?|parents?|intakes?|context|extracts?|downloads?|cache|node_modules|\.git|search|dispatch|briefs?|tasks?|primary|upstream|proof|contribution|correctness|manuscripts?|formal|\.lake|packages|build|output|checks|validation|evidence|payload|packet|logs?|tmp|temp|scratch|artifacts?|work|history|catalogue|manifest|pinned|retrievals|corpora|exports?|backups?)([-_.]|$)',re.I)
exact={'AGENTS.md','CONTENTS.md','NEW-TEN-2026-10-14.md','history-index.json','tasks.json','tree.json','preprints-tree.json'}
def excluded(n): return any(fnmatch.fnmatch(n.lower(),x) for x in active) or bool(coarse.search(n)) or n in exact
query=re.compile(r"intersective|polynomial.{0,25}(?:differences?|recurrence|curves?)|S[aá]rk[oö]zy|Lyall.{0,20}Magyar",re.I)
results=[]; count=0; omitted=[]
for start in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']:
 base=PROJECT/start
 if not base.exists(): continue
 for dp,ds,fs in os.walk(base,topdown=True,followlinks=False):
  ds[:]=sorted(d for d in ds if not excluded(d) and not (Path(dp)/d).is_symlink())
  for f in sorted(fs):
   if excluded(f): continue
   p=Path(dp)/f
   if p.is_symlink(): continue
   try: b=p.read_bytes(); s=b.decode('utf-8')
   except (OSError,UnicodeError): continue
   if '\0' in s: continue
   count+=1
   hits=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if query.search(l)]
   if hits: results.append({'path':str(p.relative_to(PROJECT)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'hits':hits})
report={'query':query.pattern,'active_patterns':active,'coarse_predicate':coarse.pattern,'named_exclusions':sorted(exact),'roots':['frontier/'+x for x in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']],'text_files_considered':count,'matched_files':results,'limits':'No size cutoff; includes hidden, ignored, JSON UTF-8. Coarse prunes omit some authored originals. Pattern false admissions possible. Counts are navigation, not clearance. No filesystem-wide or whole-parent preservation claim.'}
(ROOT/'private/history-search-polynomial.json').write_text(json.dumps(report,indent=2))
print('considered',count,'matching',len(results))
for r in results:
 print(r['path'])
 for h in r['hits'][:1]: print(' ',h['line'],h['text'][:220])

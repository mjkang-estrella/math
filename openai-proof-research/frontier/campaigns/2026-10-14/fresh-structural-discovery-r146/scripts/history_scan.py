"""Scoped UTF8 history navigation; no size cutoff; prune before descent/read."""
from pathlib import Path
import os,re,json
BASE=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=BASE/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r146'
peer=re.compile(r'(arithmetic.*r(?:112|111|110|109|108|107)|analytic.*r(?:141|140|139|138|137|136|135)|structural.*r(?:146|145|144|143)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-)',re.I)
# Deliberately coarse, including flat aliases. False omissions are reported.
blocked=re.compile(r'(corpus|sources?|primary|histor(?:y|ical)|context|catalogue|receipt|manifest|seal|tasks\.json|journal|ledger|acquire|prepare|verify|provenance|environment|bootstrap|fetch|download|pinned|packet|evidence|task|work|scratch|venv|mechanism[-_]hits|family[-_](?:titles|map|mention)|families|search|inventor|fixture|control|extract|render|vendor|build|cop(?:y|ied|ies)|frozen|role|formal|manuscript|release|parent|inputs?|private|upstream|literature|snapshot|recovery|review|contribution|intake|dispatch|brief|\.git|\.venv|node_modules|__pycache__)',re.I)
needle=re.compile(r'polymatroid|common[- ](?:integer[- ])?bases|common[- ]base|binary capacit|FPRAS|T114|I114',re.I)
counts=dict(files=0,non_utf8=0,symlinks=0,pruned_dirs=0,pruned_files=0); hits=[]
for start in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','research']:
 top=BASE/start
 if not top.is_dir():continue
 for path,dirs,files in os.walk(top,followlinks=False):
  keep=[]
  for d in dirs:
   p=Path(path)/d
   if peer.search(d) or blocked.search(d):counts['pruned_dirs']+=1
   elif p.is_symlink():counts['symlinks']+=1
   else:keep.append(d)
  dirs[:]=keep
  for f in files:
   if peer.search(f) or blocked.search(f):counts['pruned_files']+=1;continue
   p=Path(path)/f
   if p.is_symlink():counts['symlinks']+=1;continue
   try:
    b=p.read_bytes()
    if b'\0' in b:raise UnicodeError()
    s=b.decode('utf-8')
   except UnicodeError:counts['non_utf8']+=1;continue
   counts['files']+=1
   m=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if needle.search(line)]
   if m:hits.append({'path':str(p.relative_to(BASE)),'size':len(b),'matches':m})
result={'policy':'pre-descent component and pre-selection flat predicate; hidden, ignored, JSON and arbitrarily large UTF8 eligible; no exhaustive-history or isolation certificate','counts':counts,'hits':hits}
(OWN/'private/history-search-refined.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(counts));print('HIT FILES',len(hits))
for h in hits[:45]:
 print(h['path'],h['size'],len(h['matches']))
 for m in h['matches'][:3]:print(' ',m['line'],m['text'][:450])

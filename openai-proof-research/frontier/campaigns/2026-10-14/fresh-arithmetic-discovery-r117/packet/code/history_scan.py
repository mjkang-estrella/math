"""One bounded authored-history traversal. Predicates precede descent and body selection."""
from pathlib import Path
import os,fnmatch,re,json,hashlib
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117'
rounds={'structural':[151,152,150,149,148,147,146,145,144,143],'analytic':[146,147,144,143,142,141,140,139,138,137,136,135],'arithmetic':list(range(107,118))}
patterns=[f'*{k}*r{n}*' for k,ns in rounds.items() for n in ns]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
words='corpus source primary history-derivative search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot'.split()
# Additional derivative/helper aliases and shared summaries are excluded prospectively.
words += ['history-screen','history-broad','initial-history','capture','seal','progress','reading','assessment','disposition','summary','summaries','new-ten','ten-findings','twenty-findings']
exact={'.git','.venv','node_modules','__pycache__','tools'}
rx=re.compile(r'Hilbert.{0,18}tenth|diophantin|Poonen|Shlapentokh|Denef|H10|undecidab|existential.{0,30}(integer|rational)|rank.{0,16}preserv',re.I)
omit=[];errors=[];hits=[];reads=0

def reason(rel):
 s=rel.as_posix().lower()
 for pat in patterns:
  if fnmatch.fnmatchcase(s,pat):return 'round:'+pat
 for part in rel.parts:
  q=part.lower()
  if q in exact:return 'excluded:'+q
  for w in words:
   if w in q:return 'category:'+w
 return None

def walk(d):
 global reads
 with os.scandir(d) as it:
  for ent in sorted(it,key=lambda x:x.name):
   p=Path(ent.path);rel=p.relative_to(P);why=reason(rel)
   if why:omit.append([str(rel),why]);continue
   if ent.is_symlink():omit.append([str(rel),'symlink']);continue
   if ent.is_dir(follow_symlinks=False):walk(p);continue
   if not ent.is_file(follow_symlinks=False):omit.append([str(rel),'nonregular']);continue
   # Authored histories only. Filename selection follows the exclusion predicate.
   if not any(x in rel.parts for x in ['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']):
    omit.append([str(rel),'outside-authored-locations']);continue
   try:
    b=p.read_bytes();s=b.decode('utf-8');reads+=1
   except (UnicodeError,OSError) as e:errors.append([str(rel),type(e).__name__]);continue
   ls=s.splitlines();matched=[{'line':i+1,'text':line} for i,line in enumerate(ls) if rx.search(line)]
   if matched:hits.append({'path':str(rel),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'matches':matched})
walk(P)
out={'predicate_patterns':patterns,'category_substrings':words,'read_utf8':reads,'omissions':omit,'errors':errors,'hits':hits,'limits':'Raw UTF8 JSON not recursively decoded. Generic pruning can omit authored originals. No exhaustive/isolation certificate.'}
(R/'packet/private/history-selection.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'read_utf8':reads,'omitted':len(omit),'errors':len(errors),'hit_count':len(hits),'hits':[{'path':h['path'],'lines':[m['line'] for m in h['matches']]} for h in hits]},indent=2))

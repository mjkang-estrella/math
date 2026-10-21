from pathlib import Path
import os,fnmatch,re,json,hashlib
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116'
rounds=['structural*r151','analytic*r145','structural*r152','analytic*r146']+['arithmetic*r'+str(n) for n in range(107,116)]+['analytic*r'+str(n) for n in range(135,145)]+['structural*r'+str(n) for n in range(143,151)]+['h138-','t185r144-','t177c143-','t373e135-','k369r134-','t088p133-']
categories='corpus source primary history-derivative search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot'.split()
omit=[]; errors=[]; hits=[]; read=0
pattern=re.compile(r'Birch|Swinnerton|Selmer|restriction.of.scalars|Weil.restriction|isogeny.invariance|Kramer|Tate.Shafarevich|Source0*02\b|T002\b',re.I)
def banned(p):
 rel=p.relative_to(P).as_posix().lower()
 if p==R or R in p.parents:return 'own root'
 if any(fnmatch.fnmatchcase(rel,'*'+w+'*') for w in rounds):return 'round identifier'
 n=p.name.lower()
 if n in {'.git','node_modules','__pycache__','new-ten-2026-10-14.md','twenty-findings.md','package-lock.json'}:return 'infrastructure/shared journal'
 if any(c in n for c in categories):return 'protected category'
 if p.is_symlink():return 'symlink'
 return None
for base,ds,fs in os.walk(P,topdown=True,followlinks=False):
 for n in list(ds):
  p=Path(base)/n; why=banned(p)
  if why: ds.remove(n);omit.append([str(p.relative_to(P)),why])
 for n in fs:
  p=Path(base)/n;why=banned(p)
  if why:omit.append([str(p.relative_to(P)),why]);continue
  try:
   b=p.read_bytes();t=b.decode('utf8')
  except (UnicodeError,OSError) as e:errors.append([str(p.relative_to(P)),type(e).__name__]);continue
  read+=1;matches=[{'line':i,'text':s} for i,s in enumerate(t.splitlines(),1) if pattern.search(s)]
  if matches:hits.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
result={'read_utf8':read,'omissions':omit,'errors':errors,'hits':hits,'categories':categories,'rounds':rounds,'no_size_cutoff':True}
(R/'packet/private/history-scan.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'read_utf8':read,'omissions':len(omit),'errors':len(errors),'hit_files':len(hits),'paths':[h['path'] for h in hits]},indent=2))

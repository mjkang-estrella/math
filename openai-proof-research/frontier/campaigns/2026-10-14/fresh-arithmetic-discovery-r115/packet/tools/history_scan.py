from pathlib import Path
import os,fnmatch,re,json
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r115'
rounds={'structural':[150,151,149,148,147,146,145,144,143],'analytic':[145,146,144,143,142,141,140,139,138,137,136,135],'arithmetic':list(range(107,116))}
patterns=[f'*{k}*r{n}*' for k,ns in rounds.items() for n in ns]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
categories='corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party index navigation audit log'.split()
def why(n):
 s=n.lower()
 if any(fnmatch.fnmatchcase(s,p) for p in patterns): return 'round-or-identifier'
 if s in ['.git','.hg','.svn','node_modules']: return 'vcs-or-dependency'
 if 'hits' in s: return 'hits'
 for c in categories:
  if c in s: return 'category:'+c
 return None
rx=re.compile(r'p[ -]?adic section|\bI0?19\b|Tamagawa|cuspid|birational section|section.{0,60}neighbou?rhood|neighbou?rhood.{0,60}section',re.I)
omit=[];bad=[];hits=[];scanned=0
for base,ds,fs in os.walk(P,topdown=True,followlinks=False):
 kept=[]
 for d in sorted(ds):
  p=Path(base)/d; reason=why(d) or ('symlink' if p.is_symlink() else None)
  if reason: omit.append([str(p.relative_to(P)),reason])
  else: kept.append(d)
 ds[:]=kept
 for f in sorted(fs):
  p=Path(base)/f; reason=why(f) or ('symlink' if p.is_symlink() else None)
  if reason: omit.append([str(p.relative_to(P)),reason]);continue
  try: txt=p.read_bytes().decode('utf8')
  except (OSError,UnicodeError) as e: bad.append([str(p.relative_to(P)),type(e).__name__]);continue
  scanned+=1
  matches=[[i,l] for i,l in enumerate(txt.splitlines(),1) if rx.search(l)]
  if matches:hits.append({'path':str(p.relative_to(P)),'matches':matches})
out={'root':str(P),'patterns':patterns,'categories':categories,'regex':rx.pattern,'scanned':scanned,'omissions':omit,'nonutf8_errors':bad,'hits':hits,'scope':'bounded name-filtered scan, not semantic completeness or perfect isolation'}
(R/'packet/private/history-scan.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('counts',scanned,len(omit),len(bad),len(hits))
for h in hits:
 print(h['path'],len(h['matches']))
 for i,l in h['matches'][:3]: print(f' {i}: {l[:700]}')

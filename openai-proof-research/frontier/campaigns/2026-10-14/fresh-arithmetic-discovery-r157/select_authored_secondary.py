from pathlib import Path
import os,fnmatch,json,re,hashlib
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r157')
G=json.loads((ROOT/'packet/private/guards.json').read_text())
def excluded(p):
 s=p.as_posix().casefold()
 return s.startswith(G['own_root'].casefold()) or any(fnmatch.fnmatchcase(s,g) for g in G['wildcards']) or any(x in s for x in G['substrings']) or any(fnmatch.fnmatchcase(part,g) for part in s.split('/') for g in G['extra_patterns'])
alias=re.compile(r'finite[ -]volume|kobayashi|peak.function|normal.cone|siegel.domain|rescal.*automorph|bounded.*domain',re.I)
scopes={'campaigns','iterations','experiments','proposals','scouts','notes','findings'}
nav=[];count=bad=0
for base,ds,fs in os.walk('.'):
 p=Path(base)
 ds[:]=sorted(d for d in ds if not (p/d).is_symlink() and not excluded(p/d))
 for name in sorted(fs):
  q=p/name
  if excluded(q) or q.is_symlink() or not any(c.casefold() in scopes for c in q.parts):continue
  b=q.read_bytes()
  try:t=b.decode('utf8')
  except UnicodeDecodeError:bad+=1;continue
  count+=1
  hits=[]
  for m in alias.finditer(t):
   start=t.rfind('\n',0,m.start())+1;end=t.find('\n',m.end());end=len(t) if end<0 else end
   line=t[start:end]
   if not hits or hits[-1]['start']!=start:hits.append({'start':start,'line':line})
  if hits:nav.append({'path':q.as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':hits})
(ROOT/'packet/private/history-secondary-navigation.json').write_text(json.dumps({'eligible_utf8':count,'nonutf8':bad,'files':nav},indent=2)+'\n')
print('Eligible UTF8',count,'nonUTF8',bad,'hit files',len(nav))
for a in nav:
 print(a['path'],len(a['hits']))
 for h in a['hits'][:2]:print(' ',h['line'][:300])

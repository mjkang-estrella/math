from pathlib import Path
import os,fnmatch,re,json,hashlib
ROOT=Path.cwd(); OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145'
patterns=['*structural*r150*','*arithmetic*r114*','*structural*r151*','*arithmetic*r115*','*arithmetic*r116*']
patterns += [f'*analytic*r{i}*' for i in [144,143,142,141,140,139,138,137,136,135]]
patterns += [f'*structural*r{i}*' for i in [149,148,147,146,145,144,143]]
patterns += [f'*arithmetic*r{i}*' for i in [113,112,111,110,109,108,107]]
patterns += ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
categories='corpus source primary history search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party snapshot index submissions retention retrieve record_evidence'.split()
def reject(n):
 s=n.lower()
 return s in ['.git','node_modules'] or n=='fresh-analytic-discovery-r145' or any(fnmatch.fnmatchcase(s,p) for p in patterns) or any(c in s for c in categories)
query=re.compile(r'coulomb|monge|multi.?marginal|riesz.*(transport|cost)|Source\s*373|T373|self.conjugate|contact.atlas|contact.completion|five.component|mass.domination',re.I)
counts=dict(pruned=0,symlink=0,nonutf8=0,read=0,hits=0); rows=[]; skips=[]
def walk(p):
 for e in os.scandir(p):
  rel=str(Path(e.path).relative_to(ROOT))
  if reject(e.name): counts['pruned']+=1;skips.append(rel);continue
  if e.is_symlink(): counts['symlink']+=1;continue
  if e.is_dir(follow_symlinks=False): walk(Path(e.path));continue
  if not e.is_file(follow_symlinks=False):continue
  b=Path(e.path).read_bytes()
  try:
   if b'\0' in b: raise UnicodeError()
   s=b.decode('utf8')
  except UnicodeError:counts['nonutf8']+=1;continue
  counts['read']+=1
  hits=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if query.search(l)]
  if hits:rows.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':hits});counts['hits']+=len(hits)
walk(ROOT)
(OUT/'private/history-scan-corrected.json').write_text(json.dumps({'patterns':patterns,'categories':categories,'counts':counts,'hits':rows,'pruned':skips},indent=2))
print(json.dumps(counts));old={r['path'] for r in json.loads((OUT/'private/history-scan.json').read_text())['hits']};print('NEW ALIAS HIT PATHS');print('\n'.join(r['path'] for r in rows if r['path'] not in old))

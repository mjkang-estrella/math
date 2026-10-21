"""Conservative prospective authored-history search; no clearance certificate."""
from pathlib import Path
import os,fnmatch,json,re
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r150'
rounds={'arithmetic':[114,115,113,112,111,110,109,108,107], 'analytic':[144,145,143,142,141,140,139,138,137,136,135], 'structural':[150,149,148,147,146,145,144,143]}
globs=[f'*{k}*r{v}*' for k,vs in rounds.items() for v in vs]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
tokens='.venv venv site-packages __pycache__ .cache ten-findings new-ten contents readme provenance evidence prepare data downloaded .pdf .png .jpg .zip .gz index catalog tree seal corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication authenticate task work family-title prompt dispatch handoff agent review contribution snapshot session transcript factory attempt- .git node_modules'.split()
def reject(name):
 s=name.lower()
 return any(fnmatch.fnmatchcase(s,g) for g in globs) or any(t in s for t in tokens)
pat=re.compile(r'windab|matching[s -]+circuit|forest volume|Bhamidi|Horv.t|Pr[uü]fer|2-core|two-core|core.{0,30}forest|forest.{0,30}core',re.I)
counts={'utf8':0,'nonutf8':0,'nul':0,'symlink':0,'pruned':0}; hits=[]; omissions=[]
for root,dirs,files in os.walk(P,topdown=True,followlinks=False):
 allowed=[]
 for name in sorted(dirs):
  p=Path(root)/name
  if reject(name) or p.is_symlink(): counts['pruned']+=1; omissions.append(str(p.relative_to(P)))
  else: allowed.append(name)
 dirs[:]=allowed
 for name in sorted(files):
  p=Path(root)/name
  if reject(name): counts['pruned']+=1; omissions.append(str(p.relative_to(P))); continue
  if p.is_symlink(): counts['symlink']+=1; continue
  try: data=p.read_bytes(); s=data.decode('utf8')
  except UnicodeDecodeError: counts['nonutf8']+=1; continue
  if '\0' in s: counts['nul']+=1; continue
  counts['utf8']+=1
  match=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if pat.search(line)]
  if match: hits.append({'path':str(p.relative_to(P)),'matches':match})
(R/'private/history-mechanism-search.json').write_text(json.dumps({'globs':globs,'tokens':tokens,'counts':counts,'omissions':omissions,'hits':hits},indent=2))
print(counts,'hit files',len(hits))
for hit in hits:
 print(hit['path'])
 for m in hit['matches'][:2]: print(' ',m['line'],m['text'][:260])

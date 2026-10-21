# Original code, MIT. Run only from the actual project root. No writes outside OWN.
import os,fnmatch,json,re,hashlib,sys
from pathlib import Path
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
assert Path.cwd()==PROJECT
OWN=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r152')
rounds={'arithmetic':[117,118,116,115,114,113,112,111,110,109,108,107], 'analytic':[146,147,145,144,143,142,141,140,139,138,137,136,135], 'structural':[152,151,150,149,148,147,146,145,144,143]}
patterns=[f'*{family}*r{n}*' for family,ns in rounds.items() for n in ns]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
tokens='corpus source primary history-derivative search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature .venv venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence seal history ledger helper README snapshot retention capture'.lower().split()
query=re.compile(r'\bRyser\b|\bI162\b|\bT162\b|intersecting.{0,40}(?:partite|hypergraph)|truncated.{0,20}projective|merge.and.split|blocking.set.{0,25}(?:affine|plane)',re.I)
focused='--focused' in sys.argv
if focused: query=re.compile(r'resolvable|transversal.design|projective.spread|Desarguesian.spread|Wilson.{0,20}(?:construction|GDD)|fiber.{0,20}inflation|field.reduction',re.I)
counts={'eligible_utf8':0,'non_utf8':0,'nul':0,'symlinks':0,'pruned':0,'read_errors':0}
hits=[]
def denied(name):
 n=name.lower()
 return n=='.git' or any(fnmatch.fnmatchcase(n,p) for p in patterns) or any(t in n for t in tokens)
def walk(rel):
 with os.scandir(rel) as entries:
  for e in entries:
   p=Path(e.path)
   if p==OWN or denied(e.name): counts['pruned']+=1; continue
   if e.is_symlink(): counts['symlinks']+=1;continue
   if e.is_dir(follow_symlinks=False): walk(p)
   elif e.is_file(follow_symlinks=False):
    try:b=p.read_bytes()
    except OSError: counts['read_errors']+=1;continue
    try:s=b.decode('utf8')
    except UnicodeDecodeError:counts['non_utf8']+=1;continue
    if '\0' in s: counts['nul']+=1;continue
    counts['eligible_utf8']+=1
    matches=[{'line':i,'text':x} for i,x in enumerate(s.splitlines(),1) if query.search(x)]
    if matches:hits.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
walk(Path('.'))
result={'patterns':patterns,'tokens':tokens,'counts':counts,'hits':hits,'limitations':'Coarse component exclusion can omit authored material; renamed derivatives can escape. Not exhaustive or a perfect-isolation certificate.'}
(OWN/('private/history/scan-focused.json' if focused else 'private/history/scan.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':counts,'hits':[{'path':h['path'],'matches':len(h['matches'])} for h in hits]},indent=2))

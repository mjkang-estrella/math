from pathlib import Path
import os,re,json,hashlib
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r111/packet'
EX=re.compile(r'(analytic.*r(?:140|139|138|137|136|135)|structural.*r(?:146|145|144|143)|arithmetic.*r(?:111|110|109|108|107)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-)',re.I)
ROLE=re.compile(r'(\.venv|venv|site-packages|node_modules|literature|adversarial|audit|prepare|private|context|preprint|upstream|catalogue|canonical|acquisition|corpus|source|primary|histor|search|inventor|fixture|control|extract|render|vendor|build|cop(?:y|ies|ied)|frozen|role|formal|manuscript|release|parent|input|snapshot|cache|raw|evidence|reference|download|scratch|work|envelope|manifest|seal|integrity|authentication|brief|intake|review|contribution|author-result|task|title|receipt|provenance)',re.I)
NEW=re.compile(r'(?:discovery|arithmetic|analytic|structural).*?-r(\d+)',re.I)
def reject(n):
 if EX.search(n):return 'explicit isolation'
 if ROLE.search(n):return 'coarse role/body'
 m=NEW.search(n)
 if m and int(m[1])>=100:return 'coarse newer-round exclusion'
 if re.search(r'(?:proof|novelty|correctness)-r\d',n,re.I):return 'review role'
 return None
Q=re.compile(r'Donovan|\bI203\b|\bT203\w*|defect.group|Frobenius.{0,18}(?:Morita|number)|Morita.{0,30}(?:finit|bound)|(?:symmetric|basic|integral).{0,12}order|Lang.{0,25}(?:descent|integral)|(?:effective|computable).{0,35}(?:block|Morita)|(?:block|Morita).{0,35}(?:effective|computable)|Eaton.{0,15}Eisele|Pauli.{0,10}Roblot',re.I)
hits=[];om=[];scanned=[]
for base in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 root=P/'frontier'/base
 if not root.exists():om.append([str(root.relative_to(P)),'absent']);continue
 for d,dirs,files in os.walk(root,followlinks=False):
  dirs.sort();files.sort();keep=[]
  for n in dirs:
   p=Path(d)/n;why=reject(n) or ('symlink' if p.is_symlink() else None)
   if why:om.append([str(p.relative_to(P)),why])
   else:keep.append(n)
  dirs[:]=keep
  for n in files:
   p=Path(d)/n;rel=str(p.relative_to(P));why=reject(n) or ('symlink' if p.is_symlink() else None)
   if why:om.append([rel,why]);continue
   try:b=p.read_bytes();s=b.decode('utf8')
   except (UnicodeError,OSError):om.append([rel,'nonUTF8/unreadable']);continue
   if '\0' in s:om.append([rel,'NUL']);continue
   scanned.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
   ls=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if Q.search(l)]
   if ls:hits.append({'path':rel,'matches':ls})
for n,o in [('hits',hits),('omissions',om),('scanned',scanned)]: (R/'private/search'/f'{n}.json').write_text(json.dumps(o,indent=2)+'\n')
print(json.dumps({'scanned':len(scanned),'omitted':len(om),'hit_files':len(hits)}))
for x in hits:print(x['path'],len(x['matches']))

from pathlib import Path
import os,re,json,fnmatch,hashlib
P=Path('.'); R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r123'); cfg=json.loads((R/'isolation.json').read_text())
terms=cfg['coarse_component_or_subtoken_omissions']; boundary=re.compile(r'(^|[/_.\-])(?:'+ '|'.join(re.escape(x)+('s?' if x.isalpha() else '') for x in terms)+r')($|[/_.\-])',re.I)
def exclude(s):
 s=s.lower()
 if s==str(R).lower() or s.startswith(str(R).lower()+'/'):return 'own-root'
 for pat in cfg['full_path_case_insensitive_wildcards']:
  if fnmatch.fnmatchcase(s,pat):return pat
 for a in cfg['explicit_alias_substrings']:
  if a in s:return a
 if boundary.search(s):return 'coarse-category'
 return None
pat=re.compile(r'quadratic forms?|spinor|Spin\(|Margulis.{0,4}Platonov|Kneser|anisotropic.{0,40}(?:group|quadratic)',re.I)
records=[];omitted=[];errors=[];hits=[]
for here,dirs,files in os.walk(P,topdown=True,followlinks=False):
 rel=Path(here)
 keep=[]
 for name in dirs:
  p=rel/name;s=p.as_posix(); why=exclude(s)
  if rel==P and name not in cfg['root_areas']:why='root-area'
  if p.is_symlink():why='symlink'
  if why:omitted.append([s,why])
  else:keep.append(name)
 dirs[:]=keep
 for name in files:
  p=rel/name;s=p.as_posix();why=exclude(s)
  if rel==P:why='root-file'
  if p.is_symlink():why='symlink'
  if why:omitted.append([s,why]);continue
  try:
   b=p.read_bytes();txt=b.decode('utf-8')
  except (OSError,UnicodeError) as e:errors.append([s,type(e).__name__]);continue
  records.append({'path':s,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  lines=[{'line':i,'text':l} for i,l in enumerate(txt.splitlines(),1) if pat.search(l)]
  if lines:hits.append({'path':s,'matches':lines})
for name,obj in [('history-admitted',records),('history-omitted',omitted),('history-errors',errors),('history-hits',hits)]:
 (R/'private'/f'{name}.json').write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'admitted':len(records),'omitted':len(omitted),'errors':len(errors),'hit_files':len(hits),'json_files':sum(x['path'].endswith('.json') for x in records),'largest':max(x['size'] for x in records)}))
for h in hits:
 print(h['path'])
 for l in h['matches'][:2]:print(str(l['line'])+': '+l['text'][:450])

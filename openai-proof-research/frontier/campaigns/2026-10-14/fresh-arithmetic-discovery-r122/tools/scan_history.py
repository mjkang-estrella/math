from pathlib import Path
import os,re,fnmatch,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r122')
P=json.loads((R/'tools/isolation.json').read_text())
rx=re.compile(r'anticanonical|anti.canonical|zero.{0,8}Lelong|Lelong.{0,15}(zero|vanish)|controlled.boundary|bounded.metric.nonvanishing|family[ _-]*0?68|semipositive.anticanonical',re.I)
roots={'frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings'}
def reason(path):
 s=path.as_posix().casefold()
 if s==str(R) or s.startswith(str(R)+'/'):return 'own-root'
 for pat in P['active_fullpath_patterns']+P['old_fullpath_patterns']+P['special_fullpath_patterns']:
  if fnmatch.fnmatchcase(s,pat):return pat
 for term in P['coarse_path_tokens']:
  if re.search(r'(?:^|[/_.-])'+re.escape(term)+r'(?:$|[/_.-])',s):return 'coarse:'+term
 if re.search(r'terminal[_-]summary|(?:^|/)summary\.json$',s):return 'admin-alias'
 return None
hits=[];admitted=[];omitted=[];errors=[]
for base,dirs,files in os.walk('.',topdown=True,followlinks=False):
 b=Path(base)
 for n in list(dirs):
  p=b/n;why=reason(p)
  if b==Path('.') and n not in roots:why='outside-authored-roots'
  if p.is_symlink():why='symlink'
  if why:dirs.remove(n);omitted.append([str(p),why])
 for n in files:
  p=b/n;why=reason(p)
  if b==Path('.'):why='root-file-not-history'
  if p.is_symlink():why='symlink'
  if why:omitted.append([str(p),why]);continue
  try:
   raw=p.read_bytes();txt=raw.decode('utf-8')
  except Exception as e:errors.append([str(p),type(e).__name__]);continue
  admitted.append({'path':str(p),'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
  lines=[{'line':i,'text':l} for i,l in enumerate(txt.splitlines(),1) if rx.search(l)]
  if lines:hits.append({'path':str(p),'hits':lines})
res={'expression':rx.pattern,'admitted':admitted,'omitted':omitted,'errors':errors,'hits':hits}
(R/'private/history-scan-2.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n')
print('COUNTS',len(admitted),len(omitted),len(errors),len(hits))
for x in hits:
 print(x['path'])
 for l in x['hits'][:2]:print(str(l['line'])+': '+l['text'][:500])

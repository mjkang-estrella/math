import pathlib,json,hashlib,re
MODS=['Defs','Substitution','Moments','Source']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
def dependencies(r):
 pins=json.loads((r/'pins.json').read_text());out=[]
 roots=[pathlib.Path(p['path'])/'.lake/build/lib/lean' for p in pins['packages']]
 roots.append(pathlib.Path(pins['lean_binary']).parent.parent/'lib/lean')
 for mod in (r/'formal/dependencies.txt').read_text().splitlines():
  if mod in MODS:continue
  rel=pathlib.Path(*mod.split('.')).with_suffix('.olean')
  hits=[p/rel for p in roots if (p/rel).is_file()]
  assert len(hits)==1,(mod,hits)
  for ext in ['','.private','.server']:
   p=pathlib.Path(str(hits[0])+ext)
   if p.is_file():out.append({'module':mod,'path':str(p),'sha256':sha(p)})
 return sorted(out,key=lambda x:x['path'])
def audit(r):
 s=(r/'logs/FullAudit.log').read_text()
 rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',s,re.M|re.S)
 assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',s)[1])
 assert len(set(x[1] for x in rows))==len(rows)
 assert set(x[0] for x in rows)==set(MODS)
 result=[]
 for m,n,t,axs,u,p,a in rows:
  aa=re.findall(r'[\w.]+',axs)
  assert set(aa)<={'propext','Classical.choice','Quot.sound'}
  assert (u,p,a)==('false','false','false')
  result.append({'origin':m,'name':n,'actual_type':t,'axioms':aa,'unsafe':False,'partial':False,'axiom':False})
 return result

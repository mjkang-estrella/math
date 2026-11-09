import pathlib,re,hashlib,json,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
b=pathlib.Path(__file__).resolve().parent
pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
l=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux')
roots=[(b/'formal',b/'replay')]+[(p,p/'.lake/build/lib/lean') for p in pk.iterdir() if p.is_dir()]+[(l/'src/lean',l/'lib/lean')]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
queue=['Checks'];seen={};missing=[]
while queue:
 m=queue.pop()
 if m in seen:continue
 rel=pathlib.Path(*m.split('.'))
 pair=next(((s/rel.with_suffix('.lean'),o/rel.with_suffix('.olean')) for s,o in roots if (s/rel.with_suffix('.lean')).is_file()),None)
 if pair is None:missing.append(m);continue
 s,o=pair
 text=s.read_text()
 # Strip nested Lean block comments and line comments, then read module header only.
 clean=[];i=0;level=0
 while i<len(text):
  if text[i:i+2]=='/-':level+=1;i+=2
  elif level and text[i:i+2]=='-/':level-=1;i+=2
  elif level:i+=1
  elif text[i:i+2]=='--':
   j=text.find('\n',i);i=len(text) if j<0 else j
  else:clean.append(text[i]);i+=1
 text=''.join(clean)
 imports=[]
 for line in text.splitlines():
  line=line.strip()
  if not line or line in ['module','prelude']:continue
  match=re.match(r'^(?:(?:public|private)\s+)?import\s+(?:all\s+)?(.*)',line)
  if not match:break
  imports+=match[1].split()
 if not re.search(r'^prelude\s*$',text,re.M) and m!='Init':imports+=['Init']
 seen[m]={'source':str(s),'source_sha256':digest(s),'olean':str(o) if o.exists() else None,'olean_sha256':digest(o) if o.exists() else None,'imports':imports}
 queue+=imports
assert not missing,missing
(b/'dependency-hashes.json').write_text(json.dumps({'method':'recursive explicit source imports plus implicit Init; cached upstream oleans; source-only local replay','modules':seen},indent=2))
print('dependency modules',len(seen))

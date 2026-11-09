import os,json,re
from pathlib import Path
from guard import blocked,ROOT
words=re.compile(r'\b(?:Mukai|Fano|pseudoindex|pseudo-index|extremal ray|extremal rays|Picard rank|Picard number|rational curves|rational-curve|quantum cohomology|quantum divisor|unsplit|Occhetta|Bonavero|anticanonical|anti-canonical)\b',re.I)
areas={'campaigns','iterations','experiments','proposals','scouts','notes','findings'}
files=bad=0; hits=[]
for base,dirs,names in os.walk('.',topdown=True,followlinks=False):
 dirs[:]=sorted(d for d in dirs if not blocked(Path(base)/d) and not (Path(base)/d).is_symlink())
 for name in sorted(names):
  p=Path(base)/name
  if blocked(p) or p.is_symlink() or not areas.intersection(p.parts):continue
  try: t=p.read_bytes().decode('utf-8')
  except UnicodeDecodeError:bad+=1;continue
  files+=1
  ms=list(words.finditer(t))
  if not ms:continue
  snippets=[]
  for m in ms[:18]:
   a=t.rfind('\n',0,m.start())+1;b=t.find('\n',m.end()); b=len(t) if b<0 else b
   snippets.append({'line':t.count('\n',0,m.start())+1,'text':t[a:b][:600]})
  hits.append({'path':p.as_posix(),'matches':len(ms),'snippets':snippets})
(ROOT/'packet/private/authored-navigation.json').write_text(json.dumps({'utf8':files,'nonutf8':bad,'hits':hits},indent=2)+'\n')
print('Guarded UTF8 files',files,'nonUTF8',bad,'hit files',len(hits))
for h in hits:print(json.dumps(h,ensure_ascii=False))

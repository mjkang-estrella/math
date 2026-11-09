from pathlib import Path
import re,json

def strip(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
hits=[];files=list(Path('../build/formal').glob('*.lean'))
for p in files:
 s=strip(p.read_text())
 for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',s):
  hits.append(dict(file=p.name,line=s.count('\n',0,m.start())+1,token=m.group()))
r=dict(modules=len(files),hits=hits)
Path('../logs/source-scan.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

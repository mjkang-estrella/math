from pathlib import Path
import re,json
L=Path(__file__).resolve().parent.parent
# Strip nested Lean comments, line comments and quoted diagnostic strings.
def strip(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
find=[];files=list((L/'extracted').rglob('*.lean'))
for p in files:
 for n,line in enumerate(strip(p.read_text()).split('\n'),1):
  for m in re.finditer(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',line):find.append(dict(file=str(p.relative_to(L)),line=n,token=m[0]))
print(json.dumps(dict(files=len(files),findings=find),indent=2))

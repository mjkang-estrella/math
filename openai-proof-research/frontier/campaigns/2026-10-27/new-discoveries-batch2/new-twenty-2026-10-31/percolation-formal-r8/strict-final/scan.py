from pathlib import Path
import re,json,sys
r=Path(sys.argv[1]).resolve();bad=[];count=0
for p in (r/'src').glob('*.lean'):
 t=p.read_text();i=0;clean=[]
 while i<len(t):
  if t.startswith('--',i):
   j=t.find('\n',i);i=len(t) if j==-1 else j
  elif t.startswith('/-',i):
   depth=1;i+=2
   while i<len(t) and depth:
    if t.startswith('/-',i):depth+=1;i+=2
    elif t.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   assert depth==0
  elif t[i]=='"':
   i+=1
   while i<len(t):
    if t[i]=='\\':i+=2
    elif t[i]=='"':i+=1;break
    else:i+=1
  else:clean.append(t[i]);i+=1
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|\w*_unsafe_rec\w*',''.join(clean))
 if hits:bad.append({'file':p.name,'tokens':hits})
 count+=1
print(json.dumps({'files':count,'forbidden':bad},indent=2));assert not bad

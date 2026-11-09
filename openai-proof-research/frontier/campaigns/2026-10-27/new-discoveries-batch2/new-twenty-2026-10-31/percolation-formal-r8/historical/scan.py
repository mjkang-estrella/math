from pathlib import Path
import re,sys
R=Path(sys.argv[1]);count=0
for p in sorted((R/'src').glob('*.lean')):
 text=p.read_text();i=0;out=[];depth=0
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  elif text[i]=='"':
   i+=1
   while i<len(text):
    if text[i]=='\\':i+=2
    elif text[i]=='"':i+=1;break
    else:i+=1
   out.append(' ')
  else:out.append(text[i]);i+=1
 assert depth==0,p
 code=''.join(out)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|_unsafe_rec',code),p
 count+=1
print(f'Executable-token source scan passed: {count} modules.')

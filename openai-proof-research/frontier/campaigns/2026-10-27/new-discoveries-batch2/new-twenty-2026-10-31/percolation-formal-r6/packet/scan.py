import pathlib,re,json,sys
r=pathlib.Path(sys.argv[1]).resolve()
def clean(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':depth+=1;i+=2
   elif s[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:i+=1
  elif s[i:i+2]=='/-':depth=1;i+=2
  elif s[i:i+2]=='--':
   e=s.find('\n',i);i=len(s) if e<0 else e
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
find=[];files=list((r/'src').glob('*.lean'))
for p in files:
 s=clean(p.read_text())
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|\w*_unsafe_rec\w*',s)
 if hits:find.append({'file':p.name,'hits':hits})
print(json.dumps({'files':len(files),'findings':find},indent=2));sys.exit(bool(find))

import pathlib,re,sys,json
root=pathlib.Path(sys.argv[1]).resolve();bad=[];files=[]
for f in sorted((root/'src').glob('*.lean')):
 t=f.read_text();i=0;out=[];depth=0
 while i<len(t):
  if t.startswith('/-',i):
   depth=1;i+=2
   while i<len(t) and depth:
    if t.startswith('/-',i):depth+=1;i+=2
    elif t.startswith('-/',i):depth-=1;i+=2
    else:i+=1
  elif t.startswith('--',i):
   j=t.find('\n',i);i=len(t) if j<0 else j
  elif t[i]=='"':
   i+=1
   while i<len(t):
    if t[i]=='\\':i+=2
    elif t[i]=='"':i+=1;break
    else:i+=1
  else:out.append(t[i]);i+=1
 clean=''.join(out)
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|\w*_unsafe_rec\w*',clean)
 if hits:bad.append([str(f),hits])
 files.append(str(f.relative_to(root)))
print(json.dumps({'source_files':len(files),'forbidden':bad},indent=2));assert not bad

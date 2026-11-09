import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for r in range(1,52,2):
 vals=[];nxt=[]
 for k in range(1,301):
  w=r*k
  for _ in range(r):
   row=[0]*w
   for j in reversed(range(w)):
    bits=0
    if j+1<w:bits|=1<<row[j+1]
    if j<len(nxt):bits|=1<<nxt[j]
    if j+1<len(nxt):bits|=1<<nxt[j+1]
    x=0
    while bits>>x&1:x+=1
    row[j]=x
   nxt=row
  v=nxt[0];t=k%(r+2);pred=2 if not t else (0 if t%2 else 1);vals.append(v)
  if v!=pred:print('COUNTEREXAMPLE',r,k,v,pred,flush=True)
 out.append({'r':r,'k_max':len(vals),'sg':vals});(L/'outputs/king-fast-data.json').write_text(json.dumps(out));print(r,len(vals),flush=True)

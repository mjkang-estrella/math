import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for r in range(1,32,2):
 checks=[]
 for k in range(1,201):
  widths=[r*(k-i//r) for i in range(r*k)]; nxt=[]
  for w in reversed(widths):
   row=[0]*w
   for j in reversed(range(w)):
    vals=set()
    if j+1<w:vals.add(row[j+1])
    if j<len(nxt):vals.add(nxt[j])
    if j+1<len(nxt):vals.add(nxt[j+1])
    x=0
    while x in vals:x+=1
    row[j]=x
   nxt=row
  v=nxt[0];t=k%(r+2);pred=2 if t==0 else (0 if t%2 else 1)
  checks.append(v)
  if v!=pred:print('COUNTEREXAMPLE',r,k,v,pred,flush=True)
 out.append({'r':r,'k_max':len(checks),'sg':checks});print(r,len(checks),flush=True)
(L/'outputs/king-data.json').write_text(json.dumps(out))

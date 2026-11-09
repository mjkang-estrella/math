from pathlib import Path
import json,sys,time
n=int(sys.argv[1]);limit=int(sys.argv[2]);identity=bytes(range(1,n+1));seen={identity};layer=[identity]
for d in range(1,limit+1):
 start=time.time();nxt=[]
 for p in layer:
  for k in range(1,n+1):
   q=bytes(x^128 for x in p[:k][::-1])+p[k:]
   if q not in seen:seen.add(q);nxt.append(q)
 layer=nxt
 v={'n':n,'distance':d,'sphere':len(layer),'ball':len(seen),'seconds':time.time()-start}
 if d==5:v['conjectured']=n*(n-1)*(n-2)*(6*n*n-17*n+3)//6;v['matches']=len(layer)==v['conjectured']
 print(json.dumps(v),flush=True)

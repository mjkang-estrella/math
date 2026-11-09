import sys,time,json,pathlib
n=int(sys.argv[1]); start=time.time()
a=[(bytes([0]),0)]
for k in range(1,n):
 a=[(s+bytes([v]),d+(s[-1]>v)) for s,d in a for v in range(d+2)]
 print('level',k+1,'count',len(a),flush=True)
def key(s):
 p=0;out=[]
 for v in reversed(s):out.append(-v if p==0 else v);p^=(v+1)%2
 return tuple(out)
a.sort(key=lambda x:key(x[0]));worst=0;bad=[]
for (s,_),(t,_) in zip(a,a[1:]):
 ix=[i for i in range(n) if s[i]!=t[i]]
 span=ix[-1]-ix[0]+1 if ix else 0;worst=max(worst,span)
 if len(ix)>4:bad.append([list(s),list(t),ix]);break
print(json.dumps({'n':n,'count':len(a),'max_changed_span':worst,'bad':bad,'seconds':time.time()-start}),flush=True)

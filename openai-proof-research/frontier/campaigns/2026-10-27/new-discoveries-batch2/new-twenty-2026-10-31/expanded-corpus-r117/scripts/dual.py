import numpy as np,itertools,json,time,pathlib
D=pathlib.Path(__file__).resolve().parents[1];t=time.time()
V=np.array([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1]],dtype=np.int16)
rem=[x for x in range(64) if x not in (0,1,8)]; it=itertools.combinations(rem,5)
counts=np.zeros(65,dtype=np.int64); survivors=[]
# All affine-normalized subsets containing 0,(1,0),(0,1).
while True:
 chunk=list(itertools.islice(it,30000))
 if not chunk:break
 s=np.concatenate((np.tile([0,1,8],(len(chunk),1)),np.array(chunk)),axis=1);counts[0]+=len(s)
 for h in range(64):
  phase=((s%8)*(h%8)+(s//8)*(h//8))%8
  v=V[phase].sum(axis=1); a,b,c,d=v.T
  ok=((a*b+b*c+c*d-a*d)==0)&((v*v).sum(axis=1)%8==0)
  s=s[ok];counts[h+1]+=len(s)
  if not len(s):break
 survivors.extend(s.tolist())
print(json.dumps({'normalized_count':int(counts[0]),'successive_character_survivors':counts.tolist()[1:],'final_survivors':len(survivors),'seconds':time.time()-t}),flush=True)
(D/'outputs/dual-survivors.json').write_text(json.dumps(survivors))

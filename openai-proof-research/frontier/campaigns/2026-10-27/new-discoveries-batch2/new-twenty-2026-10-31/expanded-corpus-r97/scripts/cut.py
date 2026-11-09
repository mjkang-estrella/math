import numpy as np,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in range(3,8):
 for n in range(3*p+1,25):
  M=1<<n;a=np.zeros(M,dtype=np.uint8); parity=np.zeros(M,dtype=np.int8);parity[0]=1
  for i in range(n):
   L=1<<i;idx=np.arange(L,dtype=np.uint32);nb=sum(1<<j for j in range(i) if min((i-j)%n,(j-i)%n)<=p)
   a[L:2*L]=np.maximum(a[:L],1+a[idx&np.uint32((M-1)^nb)]);parity[L:2*L]=-parity[:L]
  for k in range(2,9):
   if n<(2*k-1)*p+1:continue
   f=a<k;row={'n':n,'p':p,'k':k,'dual_faces':int(f.sum()),'alternating_sum':int(parity[f].sum()),'expected':1};out.append(row);print(row,flush=True)
(D/'outputs/cut-euler.json').write_text(json.dumps(out,indent=2)+'\n')

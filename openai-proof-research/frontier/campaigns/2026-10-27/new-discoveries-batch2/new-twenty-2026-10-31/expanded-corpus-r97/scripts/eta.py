import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];N=50000;pent=[]
for j in range(1,1000):
 for g in [j*(3*j-1)//2,j*(3*j+1)//2]:
  if g<=N:pent.append(g)
pent.sort();p=[1]+[0]*N
for n in range(1,N+1):
 v=0
 for g in pent:
  if g>n:break
  v^=p[n-g]
 p[n]=v
P=int.from_bytes(bytes(sum(p[8*i+j]<<j for j in range(8) if 8*i+j<=N) for i in range((N+8)//8)),'little');mask=(1<<(N+1))-1;out=[]
for t in range(29,258,4):
 G=0;j=0
 while t*j*(j+1)//2<=N:G^=P<<(t*j*(j+1)//2);j+=1
 G &=mask;odd=[i for i in range(N+1) if (G>>i)&1];candidates=[]
 for A in range(1,129):
  seen={v%A for v in odd}
  candidates.extend([A,B] for B in range(A) if B not in seen)
 out.append({'t':t,'N':N,'odd_count':len(odd),'candidate_even_progressions_A_le128':candidates})
(D/'outputs/eta.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

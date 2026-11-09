import math,json,pathlib,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
if sys.argv[1]=='chip':
 out=[]
 for n in range(int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[3]) if len(sys.argv)>3 else 24):
  row=[2**n];lens=[]
  while row:
   lens.append(len(row));f=[x//2 for x in row];new=[f[0]]+[f[i-1]+f[i] for i in range(1,len(f))]+[f[-1]]
   while new and new[0]==0:new.pop(0)
   while new and new[-1]==0:new.pop()
   row=new
  t=1
  while t<len(lens) and lens[-t-1]==lens[-t]+1:t+=1
  z=dict(n=n,rows=len(lens),max_width=max(lens),triangle_rows=t,holds=t==max(lens)-1);out.append(z);print(z,flush=True)
  (D/('outputs/chip-'+('-'.join(sys.argv[2:]) or '1-24')+'.json')).write_text(json.dumps(out,indent=2))
else:
 S=[]
 for n in range(401):
  s=sum(math.comb(n,a)**3*sum(math.comb(n-a,b)**3 for b in range(n-a+1)) for a in range(n+1));S.append(s)
  if n>1:assert S[-1]*S[-3]>S[-2]**2
 # Exact radical elimination: S[n+1]^(n(n+2)) > S[n]^( (n+1)(n+2)/2) S[n+2]^(n(n+1)/2)
 failures=[]
 for n in range(1,100):
  if S[n+1]**(2*n*(n+2))<=S[n]**((n+1)*(n+2))*S[n+2]**(n*(n+1)):failures.append(n)
 z=dict(coverage='S(n) exact n=0..400; strict log convexity n=1..399; root-ratio decrease n=1..99',failures=failures,values=list(map(str,S)))
 (D/'outputs/multinomial.json').write_text(json.dumps(z,indent=2));print({k:v for k,v in z.items() if k!='values'})

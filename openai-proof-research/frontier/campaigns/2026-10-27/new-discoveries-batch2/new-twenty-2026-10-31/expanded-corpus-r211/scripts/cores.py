import pathlib,json,math,sys
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);p=[0]*(N+1);p[0]=1
for k in range(1,N+1):
 for n in range(k,N+1):p[n]+=p[n-k]
c={}
for t in range(4,N+1):
 # product numerator, compressed by q^t
 M=N//t;a=[0]*(M+1);a[0]=1
 for i in range(1,M+1):
  b=a[:]
  for j in range(1,min(t,M//i)+1):
   f=(-1)**j*math.comb(t,j)
   for k in range(i*j,M+1):b[k]+=f*a[k-i*j]
  a=b
 c[t]=[sum(v*p[n-t*j] for j,v in enumerate(a[:n//t+1])) for n in range(N+1)]
 if t%100==0:print('t',t,flush=True)
fail=[]
for n in range(63,N+1):
 row=[c[t+1][n]-c[t][n] for t in range(4,n-6)];down=False
 for j in range(1,len(row)):
  if row[j]<row[j-1]:down=True
  if down and row[j]>row[j-1]:fail.append({'n':n,'t':j+4,'values':row});break
out={'N':N,'all_n':list(range(63,N+1)),'t_range':'4 through n-7 inclusive','failures':fail};(D/'outputs/cores.json').write_text(json.dumps(out,indent=2)+'\n');print('failure count',len(fail),flush=True)

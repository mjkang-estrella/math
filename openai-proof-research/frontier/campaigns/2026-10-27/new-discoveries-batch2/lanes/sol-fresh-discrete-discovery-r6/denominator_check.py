import os,resource,json,pathlib,time
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
P=pathlib.Path(__file__).resolve().parent
D=[1];out=[];start=time.time()
for n in range(1,501):
 b=n;L=2
 while b%2==0:b//=2;L*=2
 E=[0]*(len(D)+(L-1)*b)
 for j in range(len(E)):E[j]=(E[j-b] if j>=b else 0)+(D[j] if j<len(D) else 0)-(D[j-L*b] if 0<=j-L*b<len(D) else 0)
 D=E;bad=[j for j in range(1,min(len(D)-1,len(D)//2+1)) if D[j]**2<D[j-1]*D[j+1]]
 out.append({'n':n,'degree':len(D)-1,'lc':not bad,'bad_first':bad[:4]})
 if bad and n not in [3,5,6,7]:
  (P/'denominator-witness.json').write_text(json.dumps({'n':n,'j':bad[0],'coefficients':D[bad[0]-1:bad[0]+2]}));print('WITNESS',n,bad[0],flush=True);break
 if n%25==0:print(n,len(D)-1,time.time()-start,flush=True);(P/'denominator-checks.json').write_text(json.dumps(out,indent=2))
(P/'denominator-checks.json').write_text(json.dumps(out,indent=2))

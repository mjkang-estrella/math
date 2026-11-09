import runpy,pathlib,json,collections,sys
L=pathlib.Path(__file__).resolve().parents[1];env=runpy.run_path(str(L/'scripts/asm_core.py'));enum=env['enumerate_poly'];n=int(sys.argv[1]);m=n//2
A=enum(n,n,(1<<n)-1);B=enum(n,m,sum(1<<j for j in range(1,n,2)));b=collections.Counter()
for (z,f),v in B.items():b[z]+=v
q={};bad=[]
for f in range(1,n+1):
 a=collections.Counter({z:v for (z,g),v in A.items() if g==f});qq={}
 while a and max(a)>=max(b):
  d=max(a)-max(b);v,rem=divmod(a[max(a)],b[max(b)])
  if rem:bad.append(('nonintegral',f,d,rem));break
  qq[d]=v
  for j,u in b.items():
   a[j+d]-=v*u
   if not a[j+d]:del a[j+d]
 if a:bad.append(('remainder',f,dict(a)))
 for d,v in qq.items():q[d,f-1]=v
out={'n':n,'ASM_count':sum(A.values()),'HSASM_count':sum(B.values()),'bad':bad,'B_next_even':[(z,f,v) for (z,f),v in q.items()]};(L/f'outputs/asm-odd-{n}.json').write_text(json.dumps(out,indent=2));print('RESULT',n,'bad',bad,flush=True)

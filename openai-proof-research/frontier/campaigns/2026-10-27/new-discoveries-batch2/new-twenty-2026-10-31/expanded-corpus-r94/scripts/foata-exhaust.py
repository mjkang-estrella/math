from parking import F,spots,D
import sys,json,time
n=int(sys.argv[1]);first=int(sys.argv[2]);count=0;fail=[];start=time.monotonic()
def visit(a,used,sp):
 global count
 if len(a)==n:
  b=F(a);q=spots(b);count+=1
  if q!=F(sp):fail.append([a,b,q,F(sp)]);print('FAIL',fail[-1],flush=True)
  if count%100000==0:print('progress',n,first,count,time.monotonic()-start,flush=True)
  return
 for p in range(1,n+1):
  if not a and p!=first:continue
  if not used>>(p-1)&1:q=p
  elif p<n and not used>>p&1:q=p+1
  else:continue
  visit(a+[p],used|1<<(q-1),sp+[q])
visit([],0,[])
r=dict(n=n,first_preference=first,complete=True,count=count,failures=fail,wall=time.monotonic()-start)
print(r,flush=True);(D/f'outputs/foata-exhaust-{n}-{first}.json').write_text(json.dumps(r,indent=2)+'\n')

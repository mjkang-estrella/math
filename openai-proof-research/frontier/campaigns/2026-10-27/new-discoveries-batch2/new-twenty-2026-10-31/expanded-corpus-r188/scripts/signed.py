import itertools,pathlib,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
n=int(sys.argv[1]);k=int(sys.argv[2]);sig=list(itertools.product([1,-1],repeat=k));counts=[0]*len(sig);t=time.monotonic()
bounds=list(itertools.combinations_with_replacement(range(n+1),k-1))
for pi in itertools.permutations(range(1,n+1)):
 h=[0]*n
 for a,b in zip(pi,pi[1:]):h[a-1]=b
 valid=[False]*len(sig)
 for bs in bounds:
  if pi[-1] in bs:continue
  es=(0,)+bs+(n,); req=[];ok=True
  for a,b in zip(es,es[1:]):
   vals=[v for v in h[a:b] if v]
   inc=all(x<y for x,y in zip(vals,vals[1:]));dec=all(x>y for x,y in zip(vals,vals[1:]));req.append((inc,dec))
   if not inc and not dec:ok=False;break
  if not ok:continue
  z=tuple(sum(p>e for e in bs) for p in pi[:-1])
  if pi[-1] not in (1,n):
   p=z[pi.index(pi[-1]+1):];q=z[pi.index(pi[-1]-1):]
   if p==q+q or q==p+p:continue
  for j,s in enumerate(sig):
   if valid[j] or any(not req[t][int(v==-1)] for t,v in enumerate(s)):continue
   if s[0]==1 and tuple(pi[-2:])==(2,1) and es[1]!=0:continue
   if s[-1]==1 and tuple(pi[-2:])==(n-1,n) and es[-2]!=n-1:continue
   if s[0]==s[-1]==-1:
    if tuple(pi[-3:])==(n-1,1,n) and not(es[1]==0 or es[-2]==n-1):continue
    if tuple(pi[-3:])==(2,n,1) and not(es[1]==0 or es[-2]==n):continue
   valid[j]=True
 for j,v in enumerate(valid):counts[j]+=v
out={'n':n,'k':k,'counts':{''.join('+' if v==1 else '-' for v in s):c for s,c in zip(sig,counts)},'counterexamples':[s for s,c in zip(sig,counts) if s!=sig[-1] and c>counts[0]],'upper_comparison':counts[0]<=counts[-1],'seconds':time.monotonic()-t}
(D/f'outputs/signed-n{n}-k{k}.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))

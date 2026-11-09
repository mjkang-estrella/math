import pathlib,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);count=nodes=0;bad=[];t=time.monotonic()
opts=[[(1<<r,1<<c) for r in range(n) for c in range(n) if n+c-r==a] for a in range(1,2*n)]
def cover(ds,rows,cols):
 global nodes
 nodes+=1
 if not ds:return True
 poss=[[(r,c) for r,c in opts[a-1] if not(r&rows or c&cols)] for a in ds]
 j=min(range(len(ds)),key=lambda j:len(poss[j]));rest=ds[:j]+ds[j+1:]
 return any(cover(rest,rows|r,cols|c) for r,c in poss[j])
def gen(pos,prev,s,seq):
 global count
 if pos==n:
  if s==n*(n-1)//2:
   ds=tuple(b+i+1 for i,b in enumerate(seq));count+=1
   if not cover(ds,0,0):bad.append(ds);print('FAIL',ds,flush=True)
  return
 for x in range(prev,n):
  if (pos+1)*pos//2<=s+x<=n*(n-1)//2 and s+x+(n-pos-1)*(n-1)>=n*(n-1)//2:gen(pos+1,x,s+x,seq+(x,))
gen(0,0,0,())
out={'n':n,'Landau_candidates':count,'exact_cover_nodes':nodes,'failures':bad,'seconds':time.monotonic()-t};print(out);(D/f'outputs/xray-cover-{n}.json').write_text(json.dumps(out,indent=2))

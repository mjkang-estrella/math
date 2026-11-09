import pathlib,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1];rows=int(sys.argv[1]);cols=int(sys.argv[2]);Q=[[0]*cols];out=[]
for i in range(1,rows+1):
 t=time.monotonic();q=[];diff=[set() for _ in range(i)];used=set()
 for j in range(cols):
  v=0
  while any(v-Q[l][j] in diff[l] for l in range(i)):v+=1
  q.append(v);used.add(v)
  for l in range(i):diff[l].add(v-Q[l][j])
 Q.append(q);mex=0
 while mex in used:mex+=1
 out.append({'row':i,'columns':cols,'max':max(q),'first_missing_nonnegative':mex,'distinct_values':len(used),'difference_distinct':list(map(len,diff)),'first_difference_gaps':[[z for z in range(-100,101) if z not in d] for d in diff[1:]],'seconds':time.monotonic()-t})
 print({k:v for k,v in out[-1].items() if k!='first_difference_gaps'},flush=True)
(D/f'outputs/difference-{rows}-{cols}.json').write_text(json.dumps(out,indent=2));(D/f'outputs/difference-{rows}-{cols}-rows.json').write_text(json.dumps(Q))

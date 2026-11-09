import pathlib,sys,functools,json
D=pathlib.Path(__file__).resolve().parents[1];k=int(sys.argv[1]);N=int(sys.argv[2]);out=[]
for n in range(N+1):
 @functools.lru_cache(None)
 def sg(mask):
  vals=set()
  for i in range(n):
   if mask>>i&1:continue
   z=mask|1<<i;r=z
   for j in range(1,k):r&=z>>j
   if not r:vals.add(sg(z))
  v=0
  while v in vals:v+=1
  return v
 v=sg(0);row=dict(k=k,n=n,sg=v,reachable_states=sg.cache_info().currsize);out.append(row);print(row,flush=True)
 (D/f'outputs/inverse-{k}.json').write_text(json.dumps(out,indent=2)+'\n')

import pathlib,sys,functools,json
D=pathlib.Path(__file__).resolve().parents[1];k=int(sys.argv[1]);N=int(sys.argv[2])
@functools.lru_cache(None)
def sg(s):
 if '0' not in s:return 0
 rev=s[::-1]
 if rev<s:return sg(rev)
 blocked=[]
 for i,c in enumerate(s):
  if c=='0' and '1'*k in s[:i]+'1'+s[i+1:]:blocked.append(i)
 if blocked:
  total=0;start=0
  for j in blocked+[len(s)]:total^=sg(s[start:j]);start=j+1
  return total
 vals={sg(s[:i]+'1'+s[i+1:]) for i,c in enumerate(s) if c=='0'}
 v=0
 while v in vals:v+=1
 return v
out=[]
for n in range(N+1):
 v=sg('0'*n);row=dict(k=k,n=n,sg=v,total_cached_states=sg.cache_info().currsize);out.append(row);print(row,flush=True)
 (D/f'outputs/inverse-split-{k}.json').write_text(json.dumps(out,indent=2)+'\n')

import functools,operator,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
L=int(sys.argv[1]);N=int(sys.argv[2]);out=[]
for total in range(L+5+(L+5)%2,N+1,2):
 @functools.lru_cache(None)
 def win(s):
  if sum(s)==total:return functools.reduce(operator.xor,s)!=0
  for i in range(L):
   if i and s[i]==s[i-1]:continue
   t=list(s);t[i]+=1;t.sort()
   if not win(tuple(t)):return True
  return False
 v=win((0,)*L);row={'tokens':total,'stacks':L,'P1wins':v,'states':win.cache_info().currsize};out.append(row);print(row,flush=True);win.cache_clear()
 (D/f'outputs/nim-{L}.json').write_text(json.dumps(out,indent=2)+'\n')

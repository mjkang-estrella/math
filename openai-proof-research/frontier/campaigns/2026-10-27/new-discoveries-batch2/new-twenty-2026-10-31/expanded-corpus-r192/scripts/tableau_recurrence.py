import pathlib,json,functools,math
D=pathlib.Path(__file__).resolve().parents[1]
# Diagnostic classical Springer Poincare recurrence; correspondence to the source inversion statistic is checked only on enumerated shapes.
@functools.lru_cache(None)
def P(s):
 if not s:return (1,)
 a=[]
 for i in range(len(s)):
  t=list(s);t[i]-=1;t=tuple(sorted((x for x in t if x),reverse=True));b=P(t)
  if len(a)<len(b)+i:a += [0]*(len(b)+i-len(a))
  for j,x in enumerate(b):a[j+i]+=x
 return tuple(a)
checks=[]
for r in json.loads((D/'outputs/tableaux-exhaustive.json').read_text()):
 for sh,c in [((r['n'],)*r['m'],r['A']),((r['n']+1,)+(r['n'],)*(r['m']-2)+((r['n']-1,) if r['n']>1 else ()),r['B'])]:
  v=tuple(reversed(P(sh)));checks.append(v==tuple(c))
assert all(checks)
rows=[]
for m in range(2,9):
 for n in range(1,13):
  if m*n>60 or math.comb(m+n,m)>30000:continue
  s=(n,)*m;t=(n+1,)+(n,)*(m-2)+((n-1,) if n>1 else ());a=P(s);b=P(t);bound=n*(m-1);fail=[k for k in range(min(bound,len(a))) if a[k]!=(b[k] if k<len(b) else 0)]
  z={'m':m,'n':n,'reflected_tail_degrees':bound,'failures':fail,'states':P.cache_info().currsize};rows.append(z);print(json.dumps(z),flush=True);(D/'outputs/tableau-recurrence.json').write_text(json.dumps({'direct_crosschecks':len(checks),'rows':rows,'status':'Diagnostic recurrence, not a proved semantic bridge'},indent=2))
 P.cache_clear()

import pathlib,json,re,math,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
counts={}
for p in (D/'logs').glob('ice*.log'):
 for e,n,c in re.findall(r'ell=(\d+) n=(\d+) count=(\d+)',p.read_text()):counts[int(e),int(n)]=int(c)
def choose(x,k):
 z=1
 for j in range(k):z=z*(x-j)//(j+1)
 return z
def diffs(a):
 v=[]
 while a:v.append(a[0]);a=[y-x for x,y in zip(a,a[1:])]
 return v
out={}
for n in range(2,13):
 lo=(n+1)//2;start=max(5,lo);ls=list(range(start,start+n+1))
 if not all((l,n) in counts for l in ls):continue
 ds=diffs([counts[l,n] for l in ls]);zero=[sum(c*choose(x-start,k) for k,c in enumerate(ds)) for x in range(n+1)];bc=diffs(zero);g=list(reversed(bc));checks={}
 for k,v in {0:1,1:0,2:2*n,3:-(n-3),4:2*n*n-5*n+11,5:-(2*n*n-11*n+19),6:(8*n**3-57*n*n+253*n-402)//6}.items():
  if k<=n:checks[k]=dict(observed=g[k],predicted=v,match=g[k]==v)
 extra={l:counts[l,n]-sum(c*choose(l-start,k) for k,c in enumerate(ds)) for l in range(start+n+1,21) if (l,n) in counts}
 out[n]=dict(interpolation_widths=ls,binomial_coefficients_g=g,source_formula_checks=checks,additional_width_residuals=extra)
print(json.dumps(out,indent=2));(D/'outputs/ice-analysis.json').write_text(json.dumps(out,indent=2)+'\n')
# Current registry path screen: not a theorem-body or worldwide prior-art clearance.
terms=['forestcut','forest_cut','schurdegree','consumption','gucycle','nonseparating','non_separating','partialsum','equitablebrooks','hanoi','squareice','regularmatroid','steinerradius','transitivetournament','approximateorbit','cliquecycle']
screen={}
for p in (D/'sources').glob('omega-*-tree.json'):
 o=json.loads(p.read_text());paths=[x['path'] for x in o.get('tree',[])];screen[p.name]=dict(truncated=o.get('truncated'),entries=len(paths),matches={s:[t for t in paths if s in t.lower().replace('_','').replace('-','')] for s in terms})
(D/'outputs/registry-path-screen.json').write_text(json.dumps(screen,indent=2)+'\n')
# Read complete context objects; output family/title summaries rather than huge audit trails.
for p in (D/'outputs').glob('context-*.json'):
 o=json.loads(p.read_text());summ=[]
 def walk(x):
  if isinstance(x,dict):
   if any(k in x for k in ['mathdb_id','related_mathdb_id']) and any(k in x for k in ['title','status','reason','scope']):summ.append({k:x[k] for k in ['mathdb_id','related_mathdb_id','title','status','reason','scope'] if k in x})
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(o);(D/'outputs'/('families-'+p.name)).write_text(json.dumps(summ,indent=2)+'\n')
# The first independent test of the cubic-in-n g_7 pattern from n=7,8,9,10.
if all(n in out for n in range(7,12)):
 ds=diffs([out[n]['binomial_coefficients_g'][7] for n in range(7,11)])
 pred=sum(v*choose(4,k) for k,v in enumerate(ds));actual=out[11]['binomial_coefficients_g'][7]
 rec=dict(training_n=[7,8,9,10],test_n=11,forward_differences=ds,predicted_g7=pred,observed_g7=actual,match=pred==actual)
 (D/'outputs/ice-g7-test.json').write_text(json.dumps(rec,indent=2)+'\n');print('g7',rec)

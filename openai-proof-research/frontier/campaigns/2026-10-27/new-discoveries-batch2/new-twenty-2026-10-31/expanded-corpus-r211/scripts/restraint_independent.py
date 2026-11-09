import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
r=[0,1,0,1,0,2,1,2,1,2,1];s=[0,1,0,1,0,1,2,1,2,0,2]
def count(r,x):
 ans=0
 for start in range(x):
  if start==r[0]:continue
  a=[int(i==start) for i in range(x)]
  for v in r[1:]:
   z=sum(a);a=[0 if i==v else z-a[i] for i in range(x)]
  ans+=sum(a)-a[start]
 return ans
j=json.loads((D/'outputs/restraints.json').read_text());p=next(a['polynomial_descending'] for a in j if a['n']==11);q=json.loads((D/'outputs/restraint-compare.json').read_text())[1]['source_polynomial_descending']
evalpoly=lambda p,x:sum(a*x**(len(p)-1-i) for i,a in enumerate(p))
out=[]
for x in range(3,31):
 a=count(r,x);b=count(s,x);assert a==evalpoly(q,x) and b==evalpoly(p,x);out.append({'colours':x,'source_count':a,'competitor_count':b,'difference':b-a})
(D/'outputs/restraint-independent.json').write_text(json.dumps(out,indent=2)+'\n');print('28 exact transfer-DP crosschecks agree; one-vertex modification, uncredited')

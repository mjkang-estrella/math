import itertools,json,pathlib,hashlib,subprocess
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
# C3 + C1: 0<1<2, isolated 3; A={2,3}.
ext=[p for p in itertools.permutations(range(4)) if p.index(0)<p.index(1)<p.index(2)]
counts=[sum(min(p.index(2),p.index(3))+1==k for p in ext) for k in range(1,5)]
assert counts==[1,1,2,0] and counts[1]**2<counts[0]*counts[2]
c=F(10,17)+F(1,17*6);assert c==F(61,102) and c<F(3,5)
out={'357065':{'executed':'enumeration of all 24 permutations, retaining the four linear extensions of C3 + C1','extensions':ext,'A':[2,3],'counts_by_position':counts,'violation':'1^2 < 1*2 at k=2; public witness in retained author survey, no credit'},'357226':{'executed':'exact rational coefficient absorption at smallest allowed n=6','c':str(c),'margin_below_three_fifths':str(F(3,5)-c),'bridge':'1/(17*n)<=1/102 for every n>=6; already source-explicit'},'357683':{'executed':'1x1 nonzero matrix [1]: pivot and input max both 1','growth_factor':'1','caveat':'literal >= endpoint defect only; no substantive discovery'}}
(P/'calculation-results.json').write_text(json.dumps(out,indent=2)+'\n')
imgs=[]
for aid,page in [('LEsurvey11',25),('2301.05202',2),('2210.17021v1',23)]:
 prefix=P/(aid+'-page'+str(page));subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-singlefile','-scale-to','1400','-png',str(P/(aid+'.pdf')),str(prefix)],check=True,timeout=20)
 p=pathlib.Path(str(prefix)+'.png');b=p.read_bytes();imgs.append({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'visual-bindings.json').write_text(json.dumps(imgs,indent=2)+'\n')
print(json.dumps(out,indent=2))

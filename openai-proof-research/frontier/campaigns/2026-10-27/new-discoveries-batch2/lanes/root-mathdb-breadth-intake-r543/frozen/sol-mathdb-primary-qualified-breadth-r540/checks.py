import pathlib,json,itertools,math
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
# Reproduce a public counterexample only; finite interpolation relies on the standard
# degree-six quasipolynomial fact, not independently proved here.
a=[1,1,2,2,2,2,13];L=26;d=6;N=26*7;v=[0]*(N+1);v[0]=1
for t in a:
 for k in range(t,N+1):v[k]+=v[k-t]
c=[]
for r in range(L):
 xs=[r+L*t for t in range(d+1)];z=F(0)
 for i,x in enumerate(xs):
  w=F(v[x])
  for j,y in enumerate(xs):
   if i!=j:w*=F(-y,x-y)
  z+=w
 c.append(z)
period=next(t for t in [1,2,13,26] if all(c[r]==c[(r+t)%26] for r in range(26)))
assert period==13
# Literal MathDB381505 K4 obstruction; source definitions differ, excluded.
forest_max=max(len(s) for n in range(5) for s in itertools.combinations(range(4),n) if len(s)<=2)
assert forest_max==2
pairs=[(524303,384,3),(526321,1296,3),(1525921777,1325424,3),(526321,216,4),(526321,36,6),(526321,6,12),(536561,6,13)]
assert all(x*x-y**n==274837012705 for x,y,n in pairs)
out={'380400':{'status':'executed public-example reproduction; not new','a':a,'degree':d,'L':L,'c0':[str(x) for x in c],'interpolated_period':period,'predicted_period':26,'limit':'Exact interpolation plus standard degree bound; not a standalone root-of-unity proof or proof-body audit'},'381505':{'status':'executed literal-wording check only','graph':'K4','largest_induced_forest':forest_max,'literal_feedback_vertex_number':2,'literal_ratio':'1','source_degree_sum_t':'1','source_LIF':2,'source_ratio':'2','credit':0},'381222':{'status':'executed validation of seven listed solutions only','all_seven_valid':True,'exhaustiveness':False}}
(P/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print('checks PASS: public period13 vs26; K4 wording only; seven listed solutions valid')

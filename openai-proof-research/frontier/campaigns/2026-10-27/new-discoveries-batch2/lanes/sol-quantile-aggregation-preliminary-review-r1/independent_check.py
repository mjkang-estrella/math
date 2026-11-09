"""Independent reconstruction; no candidate code imported or executed."""
from fractions import Fraction as Q
from pathlib import Path
import json, hashlib
D=Path(__file__).resolve().parent
c=json.loads((D/'frozen/certificate.json').read_text())
assert type(c['N']) is int and c['N']==200
assert type(c['scale']) is int and c['scale']==40000
p=c['old_permutation']; assert len(p)==200 and all(type(t) is int for t in p) and sorted(p)==list(range(200))
assert c['slopes_tenths']==[[10,13,22,28,29],[5,9,9,16,18]]
assert all(type(t) is int for row in c['slopes_tenths'] for t in row)
s=[[Q(t,10) for t in row] for row in c['slopes_tenths']]
assert all(0<row[0] and row==sorted(row) for row in s)
def quant(row,u):
    return sum(a*max(Q(0),min(Q(1,5),u-Q(k,5))) for k,a in enumerate(row))
ends=[[quant(row,Q(k,5)) for k in range(6)] for row in s]
assert ends==[[Q(0),Q(1,5),Q(23,50),Q(9,10),Q(73,50),Q(51,25)], [Q(0),Q(1,10),Q(7,25),Q(23,50),Q(39,50),Q(57,50)]]
for row,ep in zip(s,ends):
    assert sum((ep[k+1]-ep[k])/row[k] for k in range(5))==1
hx=list(map(Q,c['hx'])); hy=list(map(Q,c['hy']))
signs=[-1,-1,1,1,1,-1,-1,-1,-1,-1,1,1,-1,-1,-1,-1,-1,-1,-1,1]
assert len(hx)==len(hy)==21 and hy[0]==0
assert hx==[Q(159*k,1000) for k in range(21)]
assert [(hy[k+1]-hy[k])/(hx[k+1]-hx[k]) for k in range(20)]==signs
def payoff(t):
    return sum(signs[k]*max(Q(0),min(hx[k+1]-hx[k],t-hx[k])) for k in range(20))
assert all(payoff(x)==y for x,y in zip(hx,hy))
assert len(c['dual'])==200 and all(type(x) is str for x in c['dual'])
d=list(map(Q,c['dual'])); assert all((t*40000).denominator==1 for t in d)
u=[Q(2*k+1,400) for k in range(200)]
a=[quant(s[0],v) for v in u]; b=[quant(s[1],v) for v in u]
z=[(x+y)/2 for x,y in zip(a,b)]
slacks=[d[i]+d[j]-payoff(z[i]+z[j]) for i in range(200) for j in range(200)]
assert len(slacks)==40000 and min(slacks)>=0
A=sum(payoff(a[i]+b[p[i]]) for i in range(200))/200
B=sum(d)/100
assert A==Q(-37597,400000)==Q(c['old_midpoint_value'])
assert B==Q(-519287,4000000)==Q(c['new_midpoint_upper'])
L1=max(s[0]); L2=max(s[1]); Lr=max((x+y)/2 for x,y in zip(*s))
e_source=(L1+L2)/400; e_target=2*Lr/400
assert e_source==e_target==Q(47,4000)
gap=A-B-e_source-e_target
assert gap==Q(49317,4000000)==Q(c['certified_gap'])>0
assert Q(c['total_error_bound'])==e_source+e_target and c['positive'] is True
out={'status':'PASS','dual_inequalities':len(slacks),'minimum_slack':str(min(slacks)), 'A':str(A),'B':str(B),'source_lower':str(A-e_source),'target_upper':str(B+e_target),'continuous_gap':str(gap),'L1':str(L1),'L2':str(L2),'Lr':str(Lr),'payoff_range':[str(min(hy)),str(max(hy))], 'certificate_sha256':hashlib.sha256((D/'frozen/certificate.json').read_bytes()).hexdigest()}
(D/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

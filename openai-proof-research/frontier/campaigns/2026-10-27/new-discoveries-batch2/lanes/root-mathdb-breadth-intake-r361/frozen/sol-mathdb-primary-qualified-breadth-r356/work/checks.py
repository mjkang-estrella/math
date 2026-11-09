from pathlib import Path
import math,json
L=Path(__file__).resolve().parents[1]
Q=[1,1]
for i in range(2,13):Q.append(2*Q[-1]+Q[-2])
assert Q[2]==3 and Q[12]==19601 and math.gcd(Q[12],12)==1
assert 12%3==0 and 12%2==0 and all(Q[i]%3 for i in range(1,2))
# Exact Euclidean certificate: 19601=1633*12+5; 12=2*5+2; 5=2*2+1.
assert Q[12]==1633*12+5 and 12==2*5+2 and 5==2*2+1
(L/'bounded-checks.json').write_text(json.dumps({'mathdb_id':357242,'scope':'literal Conjecture 6.4 only; routine rank/zero-set omission, zero discovery credit','Q_0_through_Q_12':Q,'k':12,'p':3,'e_Q_p':2,'gcd':1,'rhs':True,'lhs':False,'certificate':'recurrence list and Euclidean remainder chain 5,2,1','novelty':'not investigated; no novelty claim'},indent=2)+'\n')
print('PASS exact k=12 literal counterexample; zero credit')

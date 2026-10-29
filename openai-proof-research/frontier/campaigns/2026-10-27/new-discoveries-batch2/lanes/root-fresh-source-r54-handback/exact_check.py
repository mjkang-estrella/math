from fractions import Fraction as F
from math import comb
import json
from pathlib import Path
# Exact rational enclosures certify the continuous relaxation obstruction.
assert 1122**20 < 10*1000**20
assert 1149**10 > 4*1000**10
assert F(20*1122,1000) > F(16*1149,1000)+4
# Genuine C5: S^2=5I-J.
n=5;S=[[0 if i==j else (-1 if (i-j)%n in [1,4] else 1) for j in range(n)] for i in range(n)]
S2=[[sum(S[i][k]*S[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
assert S2==[[4 if i==j else -1 for j in range(n)] for i in range(n)]
D=lambda t:(1+5*t)**4-(1+16*t)*(1+t)**4
assert D(1)>0 and D(100)<0
assert 4*15**30<16**30
q=F(21,20);a=q*(q-1)/2;deltas=[];weighted=F(0)
for k in range(2,61):
 delta=1+4*F(11,16)**k-4*F(15,16)**k
 weighted+=a*delta
 deltas.append({'k':k,'delta_sign':(delta>0)-(delta<0)})
 a=a*(k-q)/(k+1)
assert deltas[0]['delta_sign']<0 and deltas[-1]['delta_sign']>0
# Even-moment walk comparison is classical; exact small witnesses are checks only.
out={'rational_relaxation_gap_lower':str(F(20*1122,1000)-(F(16*1149,1000)+4)), 'C5_S2':S2,'determinant_difference_at_1':D(1),'determinant_difference_at_100':D(100),'moment_30_comparison':'actual>=1>4*(15/16)^30','moment_delta_signs':deltas,'weighted_partial_60_sign':(weighted>0)-(weighted<0)}
Path('exact-checks.json').write_text(json.dumps(out,indent=2));print('PASS exact obstructions and rational identities; no source refutation')

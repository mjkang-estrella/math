from pathlib import Path
import json,math
D=Path(__file__).resolve().parent
# One fixed bounded diagnostic, not an unbounded search.
p=[0]*501;p[0]=1
for k in range(1,501):
 for n in range(k,501):p[n]+=p[n-k]
hits=[];fac=1
for n in range(1,501):
 fac*=n
 if n>39 and fac%p[n]==0:hits.append({'n':n,'partition_number':p[n],'factorial_quotient':str(fac//p[n])})
# local convergence without degree bound does not control the first chromatic moment.
# clique K_m plus m^2 isolated vertices: edge/vertex tends to 1/2, isolated graph gives 0.
out={'partition_divisibility':{'range':[40,500],'executed':True,'hits':hits,'conclusion':'finite diagnostic only; no all-n theorem and no primary/prior clearance'},
'chromatic_scope_diagnostic':{'executed':True,'graphs':'K_m disjoint union m^2 isolated vertices, alternating with empty graphs of m^2+m vertices','first_moments':[{'m':m,'numerator':m*(m-1)//2,'denominator':m*m+m} for m in [10,100,1000]],'limit':'both subsequences locally approach isolated root; first moments tend to 1/2 versus 0; invalid as counterexample to bounded-degree convention'},
'power_graph_obstruction':{'executed':'hand derivation; no finite-group search','result':'An induced C4 in a power graph yields an induced P4: orient cyclic-subgroup containments alternately. For incomparable upper cyclic groups B,D with incomparable lower cyclic groups A,C, choose a prime-power cyclic subgroup E of B not in D. At least one lower group, say C, has order divisible by a different prime (otherwise A,C comparable). E,C are incomparable and E,D incomparable; generators e,b,c,d induce P4.','qualification':'Primary Kourovka question route remains parked; local short classical argument is no credited discovery; no literature clearance'} }
(D/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('partition hits',len(hits),[h['n'] for h in hits])

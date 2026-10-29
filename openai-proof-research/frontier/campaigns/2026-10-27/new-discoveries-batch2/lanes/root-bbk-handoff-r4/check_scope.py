"""Exact root checks of source indexing and the prior reconnaissance object."""
import resource, math, json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))

def quotient(num,den,N=250):
    a=[1]+[0]*N
    for d in den:
        for j in range(d,N+1):a[j]+=a[j-d]
    for d in num:
        for j in range(N,d-1,-1):a[j]-=a[j-d]
    return a

def G(k,n,N=250):
    return quotient(range(2*k-1,2*k-1+2*n,2),range(1,2*n+2,2),N)

count=0
for k in range(2,13):
    for n in range(11):
        actual=G(k,n)
        canonical=quotient(range(2*n+3,2*n+2*k-2,2),range(1,2*k-2,2))
        assert actual==canonical==G(n+2,k-2)
        count+=1
assert G(4,0)[1]==1 and G(1,3)[1]==0
assert G(2,4)==[1]*251
assert G(3,4)==quotient([11],[1,3])
# run9 has FOUR numerator factors but SIX denominator factors, including 11.
wrong=quotient([3,5,7,9],[1,3,5,7,9,11])
assert wrong[11]==2 and G(6,0)[11]==1
h4=quotient([], [1,3,5,7], 15)
h3=quotient([], [1,3,5], 15)
assert h4[15]-h4[0] != h3[15]-h3[0]
out=dict(status='PASS: corrections, not a positivity proof',identity_pairs=count,
 wrong_symmetry_witness={'k':4,'n':0,'degree':1,'actual':1,'reported_partner':0},
 run9_wrong_object={'degree':11,'actual_G6_0':1,'run9_G6_0_over_1_minus_q11':2},
 literal_k6={'numerator_count':4,'denominator':[1,3,5,7,9],'period':math.lcm(1,3,5,7,9),'denumerant_degree':4},
 lemma_2_1_ii_counterexample={'x':0,'four_part_difference':h4[15]-h4[0],'three_part_difference':h3[15]-h3[0]},
 conditional_coverage='k<=5 OR n<=3, if row certificates independently validate',
 not_established='Full Conjecture5.1; k6 positivity; independent complete row-certificate audit')
Path('scope-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

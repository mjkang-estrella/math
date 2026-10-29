from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import json

def intervals(n,i,j):
    return [(F(i,n),F(i+1,n)),(F(n*i+j,n*n),F(n*i+j+1,n*n)),(F(n*j+i,n*n),F(n*j+i+1,n*n))]

def calc(n,x,y):
    groups=defaultdict(list)
    for i in range(n):
        for j in range(n):
            boxes=intervals(n,i,j)
            groups[boxes[x]].append(boxes[y])
    ans=F(0); cdf=F(0)
    for bins in groups.values():
        m=len(bins); weight=F(m,n*n)
        absval=F(0)
        for a,b in bins:
            for c,d in bins:
                if (a,b)==(c,d): absval+=(b-a)/3
                else:
                    assert b<=c or d<=a
                    absval+=abs((a+b-c-d)/2)
        ans+=weight*3*absval/(m*m)
        cuts=sorted({F(0),F(1)}|{v for interval in bins for v in interval})
        def p(t): return sum(min(F(1),max(F(0),(t-a)/(b-a))) for a,b in bins)/m
        for a,b in zip(cuts,cuts[1:]):
            pa,pb=p(a),p(b)
            cdf+=6*weight*(b-a)*((pa+pb)/2-(pa*pa+pa*pb+pb*pb)/3)
    assert ans==cdf
    return ans

rows=[]
for n in range(2,19):
    r=F(1,n)
    expected={(0,1):r,(1,0):r,(1,2):r*r,(2,1):r*r,(2,0):r,(0,2):1-r*r+r**3}
    vals={}
    for (x,y),v in expected.items():
        actual=calc(n,x,y)
        assert actual==v and 0<actual<1
        vals[str((x,y))]=str(actual)
    direct=expected[0,2]/(expected[0,1]+expected[1,2])
    avg=(expected[0,2]+expected[2,0])/(expected[0,1]+expected[1,0]+expected[1,2]+expected[2,1])
    assert direct>F(n,4) and avg>F(n,4)
    assert n*n*n**3*F(1,n**5)==1
    rows.append(dict(n=n,distances=vals,directed_and_max_ratio=str(direct),average_ratio=str(avg)))
out=dict(status='PASS',n_range=[2,18],directed_values=102,independent_cdf_copy_comparisons=102,ratio_bounds=34,density_checks=17,rows=rows,method='conditional-copy interval absolute differences and independent piecewise affine CDF integration; no candidate code imported')
Path(__file__).with_name('independent-checks.json').write_text(json.dumps(out,indent=2))
print({k:v for k,v in out.items() if k!='rows'})

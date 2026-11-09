from pathlib import Path
import json
L=Path(__file__).parent
T={'S':('S','2'),'2':('3','4'),'3':('5','6'),'4':('3','2'),'5':('3','5'),'6':('8','7'),'7':('8','6'),'8':('8','8')}
def D(t): return 2**t+(1 if t%2==0 else 3)
# Summary stores min,max,count, all distinct internal distances, and maximum.
A={q: ((0,0,1,set(),0) if q in ('2','6') else None) for q in T}
low=[]
for t in range(121):
    P=2**t; B={}; cross={}
    for q,(u,v) in T.items():
        a,b=A[u],A[v]; gaps=set()
        if a:gaps|=a[3]
        if b:gaps|=b[3]
        if a and b:
            h=P+b[0]-a[1];gaps.add(h);cross[q]=h
        B[q]=None if not a and not b else (a[0] if a else P+b[0], P+b[1] if b else a[1],(a[2] if a else 0)+(b[2] if b else 0),gaps,max(gaps,default=0))
    if t<3:low.append({'child_depth':t,'cross':cross})
    else:
        expected={'S':4,'2':P//2+4,'3':P+2,'4':P//2+4,'5':P//2+4} if t%2==0 else {'S':6,'2':6,'4':6,'5':6}
        assert cross==expected,(t,cross,expected)
    allowed={2,4,6}|{D(s)+1 for s in range(3,t+2)}
    for q,b in B.items():
        if b:assert b[3]<=allowed,(t,q,b[3]-allowed)
    A=B
# Independent scalar recurrence from published Proposition 10, not candidate checker.
N=2**20
u=bytearray(N);u[1]=1
for n in range(3,N,2):u[n]=u[n//4] if n%4==3 else u[2*(n//4)-1]
ones=[n for n in range(N) if u[n]]
c=[a-j-1 for j,a in enumerate(ones)]
records=[];mx=0
for x,y in zip(c,c[1:]):
    h=y-x
    assert h in {1,3,5} or any(h==D(t) for t in range(3,21)),(x,h)
    if h>mx:records.append([x,h]);mx=h
F=[0,1]
for t in range(122):F.append(F[-1]+F[-2])
thresholds=[]
for t in range(3,18):
    C=5*2**t-2*F[t+2]-2
    ix=next(j for j in range(len(c)-1) if c[j+1]-c[j]>2**t)
    assert c[ix]==C and c[ix+1]-c[ix]==D(t)
    nextC=5*2**(t+1)-2*F[t+3]-2
    if t<=16:assert nextC<c[-1]
    assert all(c[j+1]-c[j]<=D(t) for j in range(ix,len(c)-1) if c[j]<nextC)
    assert [C,D(t)] in records
    thresholds.append({'t':t,'C':C,'D':D(t)})
assert [v for _,v in records if v>5]==[D(t) for t in range(3,3+len([v for _,v in records if v>5]))]
out={'status':'PASS','summary_depths':'0..121','cross_low_levels':low,'scalar_prefix_length':N,'records':records,'threshold_checks':thresholds,'fully_covered_intervals_t':'3..16 (t=17 interval checked only within prefix)','meaning':'Exact diagnostics only; the all-depth proof is in GAP-LEMMAS.md.'}
(L/'checks-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

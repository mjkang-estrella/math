from pathlib import Path
import json
L=Path(__file__).parent
T={'S':('S','2'),'2':('3','4'),'3':('5','6'),'4':('3','2'),'5':('3','5'),'6':('8','7'),'7':('8','6'),'8':('8','8')}
A={q:([0] if q in ['2','6'] else []) for q in T}
boundaries=[]
for t in range(15):
    p=2**t
    B={q:([p+min(A[s])-max(A[r])] if A[r] and A[s] else []) for q,(r,s) in T.items()}
    if t==0: assert all(not v for v in B.values())
    if t==1: assert {q:v for q,v in B.items() if v}=={'2':[2]}
    if t==2: assert {q:v for q,v in B.items() if v}=={'S':[4],'3':[6]}
    if t>=3:
        expected={'S':[6] if t%2 else [4], '2':[6] if t%2 else [p//2+4], '3':[] if t%2 else [p+2], '4':[6] if t%2 else [p//2+4], '5':[6] if t%2 else [p//2+4], '6':[], '7':[], '8':[]}
        assert B==expected
    boundaries.append({'depth':t,'boundaries':B})
    for q,(r,s) in T.items():
        gaps=lambda xs:{y-x for x,y in zip(xs,xs[1:])}
        parent=A[r]+[p+x for x in A[s]]
        assert gaps(parent)==gaps(A[r])|gaps(A[s])|set(B[q])
    A={q:A[r]+[p+x for x in A[s]] for q,(r,s) in T.items()}
# Independent scalar source recurrence, no candidate checker.
N=2**19
u=bytearray(N);u[1]=1
for n in range(3,N,2):u[n]=u[n//4] if n%4==3 else u[(n-1)//2-1]
aa=[i for i,v in enumerate(u) if v]
cc=[a-j-1 for j,a in enumerate(aa)]
gg=[y-x for x,y in zip(cc,cc[1:])]
bb=[i for i,v in enumerate(u) if not v]
g=[y-x for x,y in zip(bb,bb[1:])]
assert [i for i,v in enumerate(g) if v==2]==[c for c in cc if c<len(g)]
def accept(n):
    q='S'
    for d in bin(n)[2:]:q=T[q][int(d)]
    return q in ['2','6']
assert all(bool(v)==accept(i) for i,v in enumerate(u))
records=[];m=0
for x,d in zip(cc,gg):
    if d>m:records.append((x,d));m=d
F=[0,1]
for t in range(100):F.append(sum(F[-2:]))
thresholds=[]
for t in range(3,16):
    D=2**t+(3 if t%2 else 1);C=5*2**t-2*F[t+2]-2
    first=next((x,d) for x,d in zip(cc,gg) if d>2**t)
    assert first==(C,D);thresholds.append(first)
assert [(x,d) for x,d in records if d>5]==[(5*2**t-2*F[t+2]-2,2**t+(3 if t%2 else 1)) for t in range(3,30) if 5*2**t-2*F[t+2]-2<=records[-1][0]]
assert {d for d in gg if d<=5}=={1,3,5}
assert all(d in [1,3,5] or d in {2**t+(3 if t%2 else 1) for t in range(3,30)} for d in gg)
(L/'independent-result.json').write_text(json.dumps({'prefix_length':N,'all_states_depths':list(range(15)),'boundaries':boundaries,'records':records,'thresholds':thresholds,'status':'PASS; diagnostics only, not proof'},indent=2))
print('Independent diagnostics PASS',len(aa),'accepted positions;',records)

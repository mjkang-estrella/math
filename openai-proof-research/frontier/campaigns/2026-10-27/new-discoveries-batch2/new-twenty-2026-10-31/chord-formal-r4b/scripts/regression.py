from pathlib import Path
import itertools,json
R=Path(__file__).resolve().parent.parent

def partner(n):
    return [i+3 if i<3 else i-3 if i<6 else i+1 if i%2==0 else i-1 for i in range(2*n)]
def ribbon(t,m):
    L=len(t); rho=[]; theta=[]
    for i in range(L):
        rho.extend([3*i+j for j in ([2,0,1] if m>>i&1 else [1,2,0])])
        theta.extend([3*((i-1)%L)+1,3*((i+1)%L),3*t[i]+2])
    f=[rho[x] for x in theta]; lab=[-1]*len(f); b=0
    for x in range(len(f)):
        if lab[x]<0:
            y=x
            while lab[y]<0:
                lab[y]=b; y=f[y]
            b+=1
    return b,lab[0]==lab[3*(L-1)+1]
rows=[]
for n in range(3,8):
    t=partner(n); states=set(); genera=set(); violations=0
    for m in range(1<<(2*n)):
        b,s=ribbon(t,m); states.add((b-(n-3),s)); genera.add((n+2-b)//2)
        if n<=6:
            for e in range(4):
                bb,ss=ribbon(partner(n+1),m|(e<<(2*n)))
                expected=(b+1,s) if e in (0,3) else ((b+1,True) if s else (b-1,True))
                violations+=(bb,ss)!=expected
    assert genera=={1,2} and violations==0
    assert states=={(1,True),(3,True),(3,False)}
    rows.append(dict(n=n,assignments=1<<(2*n),states=sorted(states),genera=sorted(genera),transfer_violations=violations))
# Independent small-diagram negative controls. Each failed claim is explicit.
neg=dict(wrong_euler_offset=(1+3-ribbon(partner(3),0)[0])!=2,
         wrong_representative_genus0=ribbon([1,0,3,2,5,4],0)[0]==5,
         dropping_empty_circle=True,
         unique_at_four_refuted_in_Lean=True)
# Dart all-in permutation for one chord has one fixed cycle, plus the empty outer circle:
# b=3; deleting the empty outer circle yields 2, so 2g+b=3 has no integer g.
def dart_boundary(t,m,empty=True):
    L=len(t); side=[m>>i&1 for i in range(L)]; sig=[]
    for i in range(L):
        step=-1 if side[i] else 1; j=(i+step)%L
        while side[j]!=side[i]:j=(j+step)%L
        sig.append(j)
    p=[sig[t[i]] for i in range(L)]; seen=set(); b=0
    for i in range(L):
        if i not in seen:
            b+=1;j=i
            while j not in seen:seen.add(j);j=p[j]
    return b+(int(not any(side))+int(all(side)) if empty else 0)
neg['dropping_empty_circle']=dart_boundary([1,0],0)==3 and dart_boundary([1,0],0,False)==2
assert all(neg.values())
(R/'regression.json').write_text(json.dumps(dict(rows=rows,negative_controls=neg,numerical_only=True),indent=2)+'\n')
print(json.dumps(dict(rows=rows,negative_controls=neg)))

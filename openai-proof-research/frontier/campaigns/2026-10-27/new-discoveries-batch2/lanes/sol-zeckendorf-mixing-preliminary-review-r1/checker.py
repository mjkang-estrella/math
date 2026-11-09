"""Independent exact move-word audit; no worker code imported."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from pathlib import Path
import json

fib=[1,2,3,5,8,13,21,34]
def moves(s):
    out=[]
    def add(label,changes):
        t=list(s)
        for i,v in changes: t[i]+=v
        if min(t)>=0: out.append((label,tuple(t)))
    add('C1',[(0,-2),(1,1)])
    for i in range(1,len(s)-1):
        add('C'+str(i+1),[(i-1,-1),(i,-1),(i+1,1)])
        add('S'+str(i+1),[(i,-2),(0 if i==1 else i-2,1),(i+1,1)])
    return out
def trace(N,w):
    s=(N,)+(0,)*7; states=[s];prob=F(1)
    for a in w:
        opts=dict(moves(s));prob/=len(opts);s=opts[a];states.append(s)
    return states,prob
def reduce(w):
    r=[];i=0
    while i<len(w):
        if w[i:i+2]==('S2','C1'):r.append('C2');i+=2
        else:r.append(w[i]);i+=1
    return tuple(r)
def words(s,w=(),p=F(1)):
    opts=moves(s)
    if not opts:yield w,p;return
    for a,t in opts:yield from words(t,w+(a,),p/len(opts))
report=[];root_tests=0;weight_tests=0;boundary_successes=0
for N in range(1,11):
    cells=defaultdict(dict);total=F(0)
    for w,p in words((N,)+(0,)*7):
        total+=p;cells[reduce(w)][w]=p
        states,_=trace(N,w);C=N-sum(states[-1]);L=max([i+1 for i,a in enumerate(w) if a[0]=='S'] or [0])
        for m in range(len(w)+3):
            S=sum(a[0]=='S' for a in w[:m]);assert (len(w)<m)==(m-S>C);root_tests+=1
        # A success may begin immediately after S2; the first C1 then disappears.
        for j in range(0,len(w)-2,3):
            if w[j:j+3]==('C1','C1','C2'):
                if j and w[j-1]=='S2':boundary_successes+=1
        assert sum(w[j:j+3]==('C1','C1','C2') for j in range(0,len(w)-2,3))<=sum(a=='C2' and s[1]>=2 for a,s in zip(reduce(w),trace(N,reduce(w))[0]))
    assert total==1
    for r,cell in cells.items():
        states,base=trace(N,r);slots=[i for i,a in enumerate(r) if a=='C2' and states[i][1]>=2]
        expected={}
        for bits in product((0,1),repeat=len(slots)):
            choices=dict(zip(slots,bits));w=();ratio=F(1)
            for i,a in enumerate(r):
                if choices.get(i,0):
                    mid=dict(moves(states[i]))['S2'];ratio/=len(moves(mid));w+=('S2','C1')
                else:w+=(a,)
            assert reduce(w)==r;expected[w]=base*ratio;weight_tests+=1
        assert expected==cell
        mass=sum(cell.values());params=[F(1,1+len(moves(dict(moves(states[i]))['S2']))) for i in slots]
        assert mass==base*__import__('functools').reduce(lambda x,i:x*(1+F(1,len(moves(dict(moves(states[i]))['S2'])))),slots,F(1))
    report.append({'N':N,'words':sum(map(len,cells.values())),'cells':len(cells)})

def no_split(s,depth):
    if not depth:return F(1)
    opts=moves(s)
    if not opts:return F(1)
    return sum((no_split(t,depth-1) for a,t in opts if a[0]=='C'),F(0))/len(opts)
hazards=0
def boards(i,left,acc):
    if i==len(fib):
        if left==0:yield tuple(acc)
        return
    for h in range(left//fib[i]+1):yield from boards(i+1,left-h*fib[i],acc+[h])
for N in range(1,36):
    n=max(i+1 for i,f in enumerate(fib) if f<=N)
    for s in boards(0,N,[]):
        if sum(s)>n+2:
            assert no_split(s,3)<=1-F(1,(2*n)**3);hazards+=1
result={'status':'PASS','exact_word_cells':report,'exact_cube_weight_cases':weight_tests,'root_identity_cases':root_tests,'successes_after_S2_boundary':boundary_successes,'high_token_boards_tested':hazards,'limits':'N<=10 full words; all value<=35 boards for hazard; finite falsifier only, not asymptotic proof'}
Path(__file__).with_name('evidence.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))

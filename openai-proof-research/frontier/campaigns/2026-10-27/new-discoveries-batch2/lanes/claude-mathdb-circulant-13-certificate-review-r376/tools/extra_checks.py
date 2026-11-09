# r376 extra checks: completeness cross-method, bridge differential test, negative tests, source-construction replay,
# r360 certificate DATA comparison (JSON read as data only), DFS tree size for formal feasibility. Nonzero exit on failure.
import sys,json,random
from collections import deque
OUT,CERTDIR=sys.argv[1],sys.argv[2]; res={}
OFF={1:3,2:2,3:3,4:2,5:1,6:2,7:1,9:1}
def bfs_cn(n,S=(1,3)):
    d=[-1]*n; d[0]=0; q=deque([0])
    while q:
        u=q.popleft()
        for s in S:
            for v in ((u+s)%n,(u-s)%n):
                if d[v]<0: d[v]=d[u]+1; q.append(v)
    return d
def is_labeling(f):
    n=len(f); d=bfs_cn(n)
    return all(abs(f[i]-f[j])>=4-d[(j-i)%n] for i in range(n) for j in range(i+1,n) if d[(j-i)%n]<=3)
def okpair(a,b,e): return abs(a-b)>=OFF[e] if e in OFF else True
def valid(w): return all(okpair(w[i],w[j],j-i) for i in range(len(w)) for j in range(i+1,len(w)))
def enum_right(K,W):
    out=[];nodes=[0]
    def rec(w):
        nodes[0]+=1
        if len(w)==W: out.append(tuple(w)); return
        for a in range(K):
            if all(okpair(w[i],a,len(w)-i) for i in range(len(w))): rec(w+[a])
    rec([]); return set(out),nodes[0]
def enum_left(K,W):
    lv={()}
    for _ in range(W):
        lv={(a,)+w for w in lv for a in range(K) if valid((a,)+w)}
    return lv
for K in (11,12,13):
    R,nodes=enum_right(K,9); Lf=enum_left(K,9); assert R==Lf,K
    res[f'K{K}_windows']=len(R); res[f'K{K}_dfs_nodes_right']=nodes
    # layer sizes for formal feasibility
    res[f'K{K}_layer_sizes']=[len(enum_left(K,w)) for w in range(1,10)]
# data comparison with r360 certificates
for K in (11,12):
    d=json.load(open(f'{CERTDIR}/lab321_t3_K{K}.json'))
    theirs={tuple(s) for s in d['states']}; mine,_=enum_right(K,9)
    assert theirs==mine,K; res[f'K{K}_r360_state_set_equal']=True
# bridge differential test: random cyclic words, window-validity of all cyclic 10-windows == actual circulant labeling
rng=random.Random(376); agree=0; pos=0
for trial in range(3000):
    n=rng.randrange(19,61); K=rng.choice([12,13,14])
    if trial%3==0:   # bias toward near-valid words: perturb a periodic labeling
        base=[(5*i)%12 for i in range(n)]; f=[x if rng.random()>0.05 else rng.randrange(K) for x in base]
    else: f=[rng.randrange(K) for _ in range(n)]
    win=all(valid([f[(i+j)%n] for j in range(10)]) for i in range(n))
    assert win==is_labeling(f); agree+=1; pos+=win
res['bridge_differential']={'trials':agree,'valid_words':pos}
# negative tests: the checker must reject corrupted witnesses / non-multiples
W=json.load(open(sys.argv[3]))['witness_words']
neg=0
for L,w in W.items():
    for pos_ in (0,len(w)//2,len(w)-1):
        g=list(w); g[pos_]=g[(pos_+1)%len(g)]; assert not is_labeling(g); neg+=1
g=[(5*i)%12 for i in range(26)]; assert not is_labeling(g); neg+=1
g=[(5*i)%12 for i in range(24)]; assert is_labeling(g)
res['negative_tests_rejected']=neg
# source construction replay (Theorem 6, Obs 9, Theorem 10 as written): 12-pattern x k followed by g(r)-pattern
P12=[0,5,10,3,8,1,6,11,4,9,2,7]
txt=open(sys.argv[4]).read()
import re
seg=txt[txt.index('Observation 9.'):txt.index('Theorem 10.')]
obs={}
for n in (50,76,126,130,152):
    m=re.search(r'\n\s*%d\s+((?:\d+,\s*)+\d+)'%n,seg); nums=[int(x) for x in re.findall(r'\d+',m.group(1))]
    # pattern rows may wrap; take digits until length n
    after=seg[m.start():]; nums=[int(x) for x in re.findall(r'\d+',after)][1:]
    out=[];
    for x in nums:
        out.append(x)
        if len(out)==n: break
    obs[n]=out; assert len(out)==n and max(out)==12 and is_labeling(out),n
    assert out[:12]==P12
res['source_obs9_patterns_valid']=sorted(obs)
g={2:50,4:76,6:126,8:152,10:130}
for n in range(142,401,2):
    r=n%12
    f=P12*(n//12) if r==0 else P12*((n-g[r])//12)+obs[g[r]]
    assert len(f)==n and max(f)<=12 and is_labeling(f),n
res['source_theorem10_construction_valid_even_n']=[142,400]
# source: n in {38,64,114,118,140} claimed lambda=13; check the tail thresholds of the source construction (g(8)=152 => 140 uncovered)
json.dump(res,open(OUT,'w'),indent=1,sort_keys=True); print('PASS')

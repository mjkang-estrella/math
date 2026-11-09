# Full (non-hereditary) verification for 329080:
#  (1) GR_n for n<=6 vs source Section 3.2 table;
#  (2) bipartite interlace graph <=> min genus 0, n<=6;
#  (3) the 5-chord base lemma F5: every 5-chord diagram with max genus <= 2 has a chord crossing
#      no other chord, and the only one containing three pairwise crossing chords is (123123)(4455);
#  (4) chord-deletion lemma: deleting a chord changes the face count by exactly +-1 (n<=5, all configs).
import sys,json,itertools,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from chord import canon,prep,faces
def words(n):
    # standard labelled double-occurrence words (first occurrences increasing): (2n-1)!! of them
    def rec(w,used,nxt):
        if len(w)==2*n: yield tuple(w); return
        # positions: choose to open new letter or close an open one
        open_=[c for c in range(nxt) if w.count(c)==1]
        if nxt<n: yield from rec(w+[nxt],used,nxt+1)
        for c in open_: yield from rec(w+[c],used,nxt)
    yield from rec([],None,0)
def crosses(w,a,b):
    pa=[i for i,c in enumerate(w) if c==a]; pb=[i for i,c in enumerate(w) if c==b]
    return (pa[0]<pb[0]<pa[1])!=(pa[0]<pb[1]<pa[1])
def interlace(w):
    n=len(w)//2; return {(a,b) for a in range(n) for b in range(a+1,n) if crosses(w,a,b)}
def bipartite(n,E):
    adj={i:set() for i in range(n)}
    for a,b in E: adj[a].add(b);adj[b].add(a)
    col={}
    for s in range(n):
        if s in col: continue
        col[s]=0; st=[s]
        while st:
            v=st.pop()
            for u in adj[v]:
                if u not in col: col[u]=1-col[v]; st.append(u)
                elif col[u]==col[v]: return False
    return True
def allg(w):
    L=len(w);n=L//2;th=prep(w)
    return [ (2+n-faces(th,L,m))//2 for m in range(1<<L)]
out={}
GR={}
for n in range(1,7):
    seen={}
    for w in words(n):
        c=canon(w)
        if c in seen: continue
        gs=allg(c); seen[c]=(min(gs),max(gs),sorted(set(gs)))
    GR[n]=sorted({str(v[2]) for v in seen.values()})
    # (2)
    bad2=[]
    for c,(mn,mx,s) in seen.items():
        if (mn==0)!=bipartite(n,interlace(c)): bad2.append(c)
    out[f'n{n}']={'classes':len(seen),'GR':GR[n],'bipartite_iff_min0_failures':len(bad2)}
    if n==5:
        lst=[]; f5_fail=[]
        for c,(mn,mx,s) in seen.items():
            if mx<=2:
                E=interlace(c); iso=[a for a in range(5) if all((min(a,b),max(a,b)) not in E for b in range(5) if b!=a)]
                tri=[t for t in itertools.combinations(range(5),3) if all((x,y) in E for x,y in itertools.combinations(t,2))]
                lst.append({'word':''.join(chr(97+x) for x in c),'range':s,'isolated_chords':len(iso),'triangles':len(tri)})
                if not iso: f5_fail.append(c)
                if tri and c!=canon((0,0,1,1,2,3,4,2,3,4)): f5_fail.append(c)
        out['F5']={'maxgenus_le2_classes':lst,'count':len(lst),'failures':len(f5_fail)}
    print(n,out[f'n{n}'],flush=True)
# (4) deletion lemma on all labelled words n<=5, all configurations
dl_fail=0;dl_checked=0
for n in range(2,6):
    for w in words(n):
        L=2*n; th=prep(w)
        for x in range(n):
            pos=[i for i,c in enumerate(w) if c==x]
            w2=tuple(c if c<x else c-1 for c in w if c!=x); th2=prep(w2)
            for m in range(1<<L):
                m2=0;k=0
                for i in range(L):
                    if i in pos: continue
                    if (m>>i)&1: m2|=1<<k
                    k+=1
                d=faces(th,L,m)-faces(th2,L-2,m2); dl_checked+=1
                if abs(d)!=1: dl_fail+=1
out['deletion_lemma']={'checked':dl_checked,'failures':dl_fail}
print(out['deletion_lemma'])
out['source_table_n1_7']={'1':['[0, 1]'],'2':['[0, 1]'],'3':['[0, 1]','[0, 1, 2]','[1, 2]'],'4':['[0, 1]','[0, 1, 2]','[1, 2]'],'5':['[0, 1]','[0, 1, 2]','[0, 1, 2, 3]','[1, 2]','[1, 2, 3]'],'6':['[0, 1]','[0, 1, 2]','[0, 1, 2, 3]','[1, 2]','[1, 2, 3]']}
out['GR_matches_source']=all(sorted(out['source_table_n1_7'][str(n)])==GR[n] for n in range(1,7))
print('GR matches source:',out['GR_matches_source'])
pathlib.Path(sys.argv[1]).write_text(json.dumps(out,indent=1)+'\n')

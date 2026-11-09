# Randomised DFS with restarts for count-based HJ(k,2) colourings; incremental star-hit counters.
import sys,json,time,random
sys.path.insert(0,__file__.rsplit('/',1)[0])
from hj_counts import build
k=int(sys.argv[1]); lim=float(sys.argv[2]); seed=int(sys.argv[3]); sym=len(sys.argv)>4 and sys.argv[4]=='sym'
n=k-1; V,idx,cliques,stars=build(k,n); N=len(V); rnd=random.Random(seed)
rev=[idx[tuple(reversed(v))] for v in V]
conf=[set() for _ in range(N)]
for g in cliques:
    for x in g: conf[x].update(y for y in g if y!=x)
if sym:
    # x blue iff rev(x) blue: merge conflicts
    for x in range(N):
        if rev[x] in conf[x]: conf[x].add(x)  # self-conflict -> must be red
starsof=[[] for _ in range(N)]
for si,s in enumerate(stars):
    for x in set(s): starsof[x].append(si)
t0=time.time(); best_unc=10**9; TN=[0]; sol=None
while time.time()-t0<lim and sol is None:
    state=[0]*N; hit=[0]*len(stars); avail=[len(set(s)) for s in stars]; trail=[]
    def setv(x,v):
        # returns False on contradiction; v=1 blue, -1 red
        st=[(x,v)]
        while st:
            y,val=st.pop()
            ys=[y] if not sym else list({y,rev[y]})
            for z in ys:
                if state[z]==val: continue
                if state[z]!=0: return False
                if val==1 and z in conf[z]: return False
                state[z]=val; trail.append(z)
                if val==1:
                    for si in starsof[z]: hit[si]+=1
                    for u in conf[z]:
                        if state[u]==1: return False
                        if state[u]==0: st.append((u,-1))
                else:
                    for si in starsof[z]: avail[si]-=1
                    for si in starsof[z]:
                        if hit[si]==0:
                            if avail[si]==0: return False
                            if avail[si]==1:
                                us=[w for w in stars[si] if state[w]==0]
                                if not us: return False
                                st.append((us[0],1))
        return True
    def undo(mark):
        while len(trail)>mark:
            z=trail.pop(); v=state[z]; state[z]=0
            if v==1:
                for si in starsof[z]: hit[si]-=1
            else:
                for si in starsof[z]: avail[si]+=1
    budget=[20000]
    def dfs():
        pass
        TN[0]+=1; budget[0]-=1
        if budget[0]<0 or time.time()-t0>lim: return None
        # choose uncovered star with min avail
        bs=None;ba=99
        for si in range(len(stars)):
            if hit[si]==0 and avail[si]<ba:
                ba=avail[si]; bs=si
                if ba<=2: break
        if bs is None: return True
        cands=[x for x in set(stars[bs]) if state[x]==0]
        cands.sort(key=lambda x:(-sum(1 for si in starsof[x] if hit[si]==0)+rnd.random()*2))
        for x in cands:
            mark=len(trail)
            if setv(x,1):
                r=dfs()
                if r is not False: return r
            undo(mark)
            if not setv(x,-1): undo(mark); return False
        return False
    r=dfs()
    if r is True:
        sol=[V[i] for i in range(N) if state[i]==1]
    unc=sum(1 for si in range(len(stars)) if hit[si]==0)
out=dict(k=k,sym=sym,seed=seed,nodes=TN[0],secs=round(time.time()-t0,1),found=sol is not None)
if sol:
    Bs=set(sol); out['verified']=all(any(V[x] in Bs for x in s) for s in stars) and all(sum(V[x] in Bs for x in g)<=1 for g in cliques); out['B']=sol
print(json.dumps(out))

# Minimal CDCL SAT solver (pure Python; 2-watched literals, 1-UIP learning, VSIDS-like activity, Luby restarts).
# Written for this lane; used only for small structured instances. Literals are +/-(var+1).
import sys,time,random
class Solver:
    def __init__(s,nv,clauses,seed=0):
        s.nv=nv; s.cl=[]; s.watch={}; s.assign=[0]*(nv+1); s.level=[0]*(nv+1); s.reason=[None]*(nv+1)
        s.trail=[]; s.lim=[]; s.act=[0.0]*(nv+1); s.inc=1.0; s.rnd=random.Random(seed); s.phase=[-1]*(nv+1)
        s.qhead=0; s.ok=True; s.conflicts=0
        for c in clauses:
            c=list(dict.fromkeys(c))
            if not c: s.ok=False; return
            if len(c)==1:
                if not s.enqueue(c[0],None): s.ok=False
                continue
            s.add(c)
    def add(s,c):
        i=len(s.cl); s.cl.append(c)
        s.watch.setdefault(-c[0],[]).append(i); s.watch.setdefault(-c[1],[]).append(i)
        return i
    def val(s,l):
        a=s.assign[abs(l)]
        return a if l>0 else -a
    def enqueue(s,l,r):
        v=s.val(l)
        if v==-1: return False
        if v==1: return True
        x=abs(l); s.assign[x]=1 if l>0 else -1; s.level[x]=len(s.lim); s.reason[x]=r; s.trail.append(l); return True
    def propagate(s):
        while s.qhead<len(s.trail):
            l=s.trail[s.qhead]; s.qhead+=1
            ws=s.watch.get(l,[]); keep=[]; i=0; conflict=None
            while i<len(ws):
                ci=ws[i]; i+=1; c=s.cl[ci]
                if c[0]==-l: c[0],c[1]=c[1],c[0]
                if s.val(c[0])==1: keep.append(ci); continue
                found=False
                for k in range(2,len(c)):
                    if s.val(c[k])!=-1:
                        c[1],c[k]=c[k],c[1]; s.watch.setdefault(-c[1],[]).append(ci); found=True; break
                if found: continue
                keep.append(ci)
                if not s.enqueue(c[0],ci):
                    conflict=ci; keep.extend(ws[i:]); break
            s.watch[l]=keep
            if conflict is not None: return conflict
        return None
    def analyze(s,ci):
        seen=set(); learnt=[None]; counter=0; p=None; idx=len(s.trail)-1; lvl=len(s.lim)
        while True:
            c=s.cl[ci]
            for q in (c if p is None else c[1:]) if True else c:
                x=abs(q)
                if q==p: continue
                if x not in seen and s.level[x]>0:
                    seen.add(x); s.bump(x)
                    if s.level[x]>=lvl: counter+=1
                    else: learnt.append(q)
            while abs(s.trail[idx]) not in seen: idx-=1
            p=s.trail[idx]; idx-=1; ci=s.reason[abs(p)]; seen.discard(abs(p)); counter-=1
            if counter==0: break
            c=s.cl[ci]
            if c[0]!=p:
                j=c.index(p); c[0],c[j]=c[j],c[0]
        learnt[0]=-p
        bt=0 if len(learnt)==1 else max(s.level[abs(q)] for q in learnt[1:])
        if len(learnt)>1:
            j=max(range(1,len(learnt)),key=lambda t:s.level[abs(learnt[t])]); learnt[1],learnt[j]=learnt[j],learnt[1]
        return learnt,bt
    def bump(s,x):
        s.act[x]+=s.inc
        if s.act[x]>1e100:
            s.act=[a*1e-100 for a in s.act]; s.inc*=1e-100
    def backtrack(s,lv):
        if len(s.lim)>lv:
            for l in s.trail[s.lim[lv]:]:
                x=abs(l); s.phase[x]=s.assign[x]; s.assign[x]=0; s.reason[x]=None
            del s.trail[s.lim[lv]:]; del s.lim[lv:]; s.qhead=len(s.trail)
    def pick(s):
        best=None;ba=-1.0
        for x in range(1,s.nv+1):
            if s.assign[x]==0 and s.act[x]>ba: ba=s.act[x];best=x
        return best
    def solve(s,limit):
        if not s.ok: return False
        t0=time.time(); restart=100; nconf=0
        while True:
            ci=s.propagate()
            if ci is not None:
                s.conflicts+=1; nconf+=1
                if not s.lim: return False
                learnt,bt=s.analyze(ci); s.backtrack(bt)
                if len(learnt)==1: s.enqueue(learnt[0],None)
                else:
                    i=s.add(learnt); s.enqueue(learnt[0],i)
                s.inc*=1.05
                if time.time()-t0>limit: return None
            else:
                if nconf>=restart:
                    nconf=0; restart=int(restart*1.3); s.backtrack(0); continue
                x=s.pick()
                if x is None: return True
                s.lim.append(len(s.trail)); s.enqueue(x if s.phase[x]==1 else -x,None)
    def model(s): return [s.assign[x]==1 for x in range(1,s.nv+1)]

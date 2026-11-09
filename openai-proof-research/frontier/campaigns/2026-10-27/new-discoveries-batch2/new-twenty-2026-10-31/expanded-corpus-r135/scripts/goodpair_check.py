import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from gadget import make
Barcs=[(0,1),(0,2),(3,0),(1,2),(1,3),(3,1),(2,3)]
def branchings(n, arcs, s):
    ins=[[u for (u,v) in arcs if v==w] for w in range(n)]
    others=[v for v in range(n) if v!=s]
    def rec(i,ch):
        if i==len(others):
            ok=True
            for v in others:
                seen=set(); w=v
                while w!=s:
                    if w in seen: ok=False; break
                    seen.add(w); w=ch[w]
                if not ok: break
            if ok: yield {(ch[v],v) for v in others}
            return
        v=others[i]
        for u in ins[v]:
            ch[v]=u
            yield from rec(i+1,ch)
        del ch[v]
    yield from rec(0,{})
def all_reach_t(n, arcs, t):
    inn=[[] for _ in range(n)]
    for (u,v) in arcs: inn[v].append(u)
    seen={t}; st=[t]
    while st:
        x=st.pop()
        for y in inn[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen)==n
for M in (2,3):
    arcs=make(M,4,Barcs,[(0,0),(1,2)],[(2,0),(2,2 if M>2 else 1)])
    n=M+4
    for s in range(M):
        Bs=list(branchings(n,arcs,s))
        res={t: any(all_reach_t(n,[a for a in arcs if a not in B],t) for B in Bs) for t in range(n)}
        print('M',M,'s',s,'#branchings',len(Bs),'good pair (B_s^+,B_t^-) exists for t:',res,flush=True)

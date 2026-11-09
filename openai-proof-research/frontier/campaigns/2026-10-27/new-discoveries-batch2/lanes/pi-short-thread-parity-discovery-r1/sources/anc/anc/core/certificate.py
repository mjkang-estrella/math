"""Write a human-checkable certificate for g(S(x1,...,xk)) using Proposition 6.1:
every reachable spider state with its options and value.  Usage: certificate.py 1 3 7"""
import sys
from functools import lru_cache
xs=tuple(int(a) for a in sys.argv[1:])
def B(k): return k
def run_near(h,d,phi):   # rho(h; d, phi)
    if h==0: return 0
    if phi=='*': return h
    if phi==d: return h&1
    return 1 if (h>=2 and h%2==0) else 0
def run_free(h,phi):     # leg detaching from a free centre
    if h==0: return 0
    if phi=='*': return h&1
    return h
UPD={('n','in'):'i',('n','out'):'o',('i','in'):'i',('i','out'):'f',('o','in'):'f',('o','out'):'o'}
def settle(s,L):
    if s=='f':
        x=0
        for (h,phi) in L: x^=run_free(h,phi)
        return x, None
    if not L: return 0,None
    if len(L)==1 and s in 'io':
        (h,phi),=L
        return run_near(h,'out' if s=='i' else 'in',phi), None
    return None,(s,tuple(sorted(L)))
states={}
def gamma(s,L):
    key=(s,tuple(sorted(L)))
    if key in states: return states[key][0]
    opts=[]
    L=list(key[1])
    for t,(h,phi) in enumerate(L):
        rest=L[:t]+L[t+1:]
        for j in range(1,h+1):
            for d in ('in','out'):
                if j==h and phi!='*' and d!=phi: continue
                det=run_near(h-j,d,phi)
                if j>=2:
                    v,k=settle(s,rest+[(j-1,d)])
                else:
                    v,k=settle(UPD[(s,d)],rest)
                val=v if k is None else gamma(*k)
                opts.append(("leg(%d,%s) edge %d %s"%(h,phi,j,d), det, val, det^val))
    g=0
    S={o[3] for o in opts}
    while g in S: g+=1
    states[key]=(g,opts)
    return g
g=gamma('n',[(x,'*') for x in xs])
def fmt(key):
    s,L=key
    return "(%s; %s)"%(s,", ".join("%d%s"%(h,{'*':'*','in':'<','out':'>'}[phi]) for h,phi in L))
lines=["Certificate for g(S%s) = %d via Proposition 6.1."%(str(xs),g),
       "Notation: state (s; h phi, ...): centre status s, attached legs with h unmarked edges and far end phi:",
       "  * free, < blocked IN (towards centre), > blocked OUT.  Each option: detached-run value XOR new-state value = option value.",
       "Number of states: %d"%len(states),""]
for key in sorted(states, key=lambda k:(sum(h for h,_ in k[1]),k)):
    val,opts=states[key]
    lines.append("%s = %d   options: %s"%(fmt(key),val," ".join(str(o[3]) for o in opts)))
open("certificate_S%s.txt"%("_".join(map(str,xs))),"w").write("\n".join(lines)+"\n")
print(g,len(states))

"""Weakened finite claims for Lean: T = one chosen in-arc (in W1) for each q != e, NO acyclicity.
W1 on {0,1,2,3}: 0->1,1->2,2->3,3->0,0->2,1<->3.
Case e=0: claim no parent choice makes W1 - T strongly connected.
Case e=2: claim no parent choice gives (0 reaches all of B) and (all reach 2) in W1 - T."""
import itertools
W=[(0,1),(1,2),(2,3),(3,0),(0,2),(1,3),(3,1)]
def reach(arcs,s,rev=False):
    seen={s};st=[s]
    while st:
        x=st.pop()
        for (u,v) in arcs:
            a,b=(v,u) if rev else (u,v)
            if a==x and b not in seen: seen.add(b);st.append(b)
    return seen
def choices(e):
    qs=[q for q in range(4) if q!=e]
    return [dict(zip(qs,p)) for p in itertools.product(*[[u for (u,w) in W if w==q] for q in qs])]
full={0,1,2,3}
c1=[(sorted((p,q) for q,p in ch.items()), reach([a for a in W if a not in {(p,q) for q,p in ch.items()}],0)==full and reach([a for a in W if a not in {(p,q) for q,p in ch.items()}],0,True)==full) for ch in choices(0)]
c2=[]
for ch in choices(2):
    T={(p,q) for q,p in ch.items()}; R=[a for a in W if a not in T]
    c2.append((sorted(T), reach(R,0)==full and reach(R,2,True)==full))
print('case e=0: parent choices',len(c1),'any good:',any(g for _,g in c1))
print('case e=2: parent choices',len(c2),'any good:',any(g for _,g in c2))
# Monotone subset form used by the Lean draft: all T subset of W1 with T-reach(e) = B.
bad1=bad2=0;n1=n2=0
for mask in range(1<<7):
    T={W[i] for i in range(7) if mask>>i&1}; R=[a for a in W if a not in T]
    if reach(list(T),0)==full:
        n1+=1
        if reach(R,0)==full and reach(R,0,True)==full: bad1+=1
    if reach(list(T),2)==full:
        n2+=1
        if reach(R,0)==full and reach(R,2,True)==full: bad2+=1
print('subset form e=0: spanning T',n1,'counterexamples',bad1,'| e=2: spanning T',n2,'counterexamples',bad2)

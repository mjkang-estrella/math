"""Generate DIMACS CNF for 2-colour ordered/cyclic Ramsey problems (Poljak/Kissat encoding of arXiv:2604.16188 Sec. 3).
Variable x_{u,v} (u<v) TRUE means edge coloured with colour 2. Colour-1 graph H1 forbidden, colour-2 graph H2 forbidden.
usage: ramsey_sat.py MODE(ord|cyc) H1 H2 n out.cnf ; graphs: K:a, Pmon:a, Palt:a, Cmon:a, S:a (start-central star), Mnest:a
"""
import sys,itertools
def graph(spec):
    t,a=spec.split(':');a=int(a)
    if t=='K': E=[(i,j) for i in range(a) for j in range(i+1,a)]
    elif t=='Pmon': E=[(i,i+1) for i in range(a-1)]
    elif t=='Cmon': E=[(i,i+1) for i in range(a-1)]+([(0,a-1)] if a>=3 else [])
    elif t=='Palt':
        seq=[];lo,hi=0,a-1
        while lo<=hi:
            seq.append(lo)
            if hi!=lo: seq.append(hi)
            lo+=1;hi-=1
        E=[tuple(sorted(p)) for p in zip(seq,seq[1:])]
    elif t=='Palt_seq': raise SystemExit
    elif t=='S': E=[(0,j) for j in range(1,a)]
    elif t=='Mnest': E=[(v,a-1-v) for v in range(a//2)]
    else: raise SystemExit('bad '+t)
    return a,E
def var(u,v,n):
    if u>v:u,v=v,u
    return u*n-u*(u+1)//2+(v-u-1)+1
def tuples(k,n,mode):
    for c in itertools.combinations(range(n),k):
        if mode=='ord': yield c
        else:
            seen=set()
            for t in range(k):
                r=c[t:]+c[:t]  # r[0]=phi(0) ... r is phi listed by H-vertex index after rotation
                # phi(j) for j: the H vertex ordering rotated: need phi(t'),...,phi(k-1),phi(0).. increasing
                # equivalently phi = c rotated by t: phi(j)=c[(j - s) mod k] for shift s
                if r not in seen: seen.add(r); yield r
def main():
    mode,h1,h2,n,out=sys.argv[1:6];n=int(n)
    a,E1=graph(h1);b,E2=graph(h2)
    cl=set()
    for w in tuples(a,n,mode):
        cl.add(tuple(sorted({var(w[u],w[v],n) for u,v in E1})))
    for w in tuples(b,n,mode):
        cl.add(tuple(sorted({-var(w[u],w[v],n) for u,v in E2})))
    with open(out,'w') as f:
        f.write(f'p cnf {n*(n-1)//2} {len(cl)}\n')
        for c in cl: f.write(' '.join(map(str,c))+' 0\n')
    print(mode,h1,h2,n,'vars',n*(n-1)//2,'clauses',len(cl),'E1',E1,'E2',E2)
if __name__=='__main__':main()

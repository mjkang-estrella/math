# Sweep: G bad (gamma_d^p(G)=inf, connected, order<=nG), H connected order<=nH without (d,p)-close vertex; test G strong H.
import sys,json,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve
def parse(s):
    s=s.strip(); n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63
        for k in range(5,-1,-1): bits.append((v>>k)&1)
    adj=[[] for _ in range(n)]; idx=0
    for j in range(1,n):
        for i in range(j):
            if bits[idx]: adj[i].append(j); adj[j].append(i)
            idx+=1
    return adj
def load(n):
    return [l.strip() for l in open(f'sources/graphdata/graph{n}c.g6') if l.strip()]

# Portable adapter: unchanged mathematical loops of inherited/reviewer.py.
# Repository authentication and receipt writing removed; see PROVENANCE.md. MIT.
"""Independent finite stress checks, not a proof of S2. Original code MIT."""
from itertools import combinations, product
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
AUTHOR=ROOT.parent/'fresh-arithmetic-discovery-r4'
def sha(b):return hashlib.sha256(b).hexdigest()
def image(adj,S):return set().union(*(adj[v] for v in S)) if S else set()
def subsets(X):
    X=list(X)
    for mask in range(1<<len(X)):yield {x for i,x in enumerate(X) if mask>>i&1}
def graphs(n):
    pairs=list(combinations(range(n),2))
    for states in product(range(3),repeat=len(pairs)):
        out=[set() for _ in range(n)]
        for (u,v),state in zip(pairs,states):
            if state==1:out[u].add(v)
            if state==2:out[v].add(u)
        yield out

def main():
    deletion=blowup=anchors=0
    for n in (3,4):
      V=set(range(n))
      for out in graphs(n):
        for S in subsets(V):
          if not S or S==V:continue
          I=image(out,S)&S;E=image(out,S)-S
          for T in subsets(E):
            if T==E:continue
            changed=[N-(E-T) if x in S else N.copy() for x,N in enumerate(out)]
            for v in S:
              Q=out[v]&(E-T)
              if not Q:continue
              C=image(out,Q)-(I|T|Q|image(out,T))
              old2=image(out,out[v])-out[v]-{v}
              new2=image(changed,changed[v])-changed[v]-{v}
              assert C<=old2 and not C&new2
              assert new2-old2<=Q&image(out,T)
              assert len(new2)<=len(old2)-len(C)+len(Q&image(out,T))
              inc=len(image(out,T|Q)-(I|T|Q))-len(image(out,T)-(I|T))
              assert inc==len(C)-len(Q&image(out,T))
              deletion+=1
        m=3 if n==3 else 2
        X={(p,a) for p in V for a in range(m)}
        G={x:{y for y in X if y[0] in out[x[0]] or y[0]==x[0] and y[1]>x[1]} for x in X}
        for U in subsets(X):
          if not U or U==X:continue
          S={p for p,a in U};A=image(out,S);B=image(out,A)
          JU=image(G,U);J2=image(G,JU)
          val=len(U)+len(J2)-2*len(JU)
          assert val<=m*(len(B-A)-len(A-S))+len(S-A)
          blowup+=1
          for w in V:
            for a in range(1,m):
              j=(w,a)
              if j in U and j not in J2:
                assert w not in A|B
                anchors+=1
    return {'deletion_endpoint_cases':deletion,'blowup_subset_cases':blowup,'anchor_exclusion_cases':anchors}
if __name__=='__main__':print(json.dumps(main(),sort_keys=True))

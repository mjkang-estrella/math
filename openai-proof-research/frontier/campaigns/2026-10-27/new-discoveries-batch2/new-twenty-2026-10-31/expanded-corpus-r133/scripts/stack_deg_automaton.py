# Independent check of d_n via left-to-right simulation of both postorder stack processes.
# State: tuple of blocks (length, #B-stack items, #B'-stack items); blocks separated by common boundaries.
# Step j: B pops t in {0,1,2} items (mult 1,2,1), B' pops u; touched blocks merge with node j;
# weight 1/h_j, h_j = 1 + total length of touched blocks. Final: one block with (n,1,1).
import sys
from fractions import Fraction
from collections import defaultdict
mu={0:1,1:2,2:1}
N=int(sys.argv[1])
cur={():Fraction(1)}
for j in range(1,N+1):
    nxt=defaultdict(Fraction)
    for st,w in cur.items():
        totb=sum(b for _,b,_ in st); totc=sum(c for _,_,c in st)
        for t in (0,1,2):
            if t>totb: continue
            for u in (0,1,2):
                if u>totc: continue
                if t==0 and u==0:
                    nxt[st+((1,1,1),)]+=w; continue
                # find earliest touched block
                k=len(st); rb=t; rc=u
                while rb>0 or rc>0:
                    k-=1; L,b,c=st[k]
                    rb-=b; rc-=c
                # blocks k..end touched; remaining items in block k: max(0,-rb) B-items? compute exactly
                remb=-rb if rb<0 else 0; remc=-rc if rc<0 else 0
                # items of touched blocks other than popped: only block k can retain items
                L=sum(x[0] for x in st[k:])
                nxt[st[:k]+((L+1,remb+1,remc+1),)]+=w*mu[t]*mu[u]/(L+1)
    cur=nxt
    d=sum(w for st,w in cur.items() if len(st)==1 and st[0][1]==1 and st[0][2]==1)
    print(j, d, len(cur), flush=True)

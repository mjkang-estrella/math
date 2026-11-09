# Max k-crossing-free antichain in {0..R}^w via max-clique branch and bound (Tomita-style colouring bound).
import sys,itertools,time,json
k=int(sys.argv[1]); w=int(sys.argv[2]); R=int(sys.argv[3]); target=int(sys.argv[4]); tlim=float(sys.argv[5])
V=list(itertools.product(range(R+1),repeat=w)); N=len(V)
def compat(A,B):
    pos=neg=False; bigp=bign=False
    for a,b in zip(A,B):
        d=a-b
        if d>0:
            pos=True
            if d>=k: bigp=True
        elif d<0:
            neg=True
            if d<=-k: bign=True
    return pos and neg and not(bigp and bign)
nb=[0]*N
for i in range(N):
    for j in range(i+1,N):
        if compat(V[i],V[j]): nb[i]|=1<<j; nb[j]|=1<<i
deg=[x.bit_count() for x in nb]
best=[-1]*(target-1) if len(sys.argv)>6 and sys.argv[6]=="seek" else []; start=time.time(); nodes=0; timed_out=False
def colour_sort(P):
    # greedy colouring of candidate set P (bitset); returns list of (vertex,colour) in colour order
    order=[]; col=0; U=P
    while U:
        col+=1; Q=U
        while Q:
            v=(Q&-Q).bit_length()-1; Q&=~(1<<v); Q&=~nb[v]; U&=~(1<<v); order.append((v,col))
    return order
VAL=[0]*(R+1)
for i in range(N): VAL[V[i][0]]|=1<<i
COVER=len(sys.argv)>10 and sys.argv[10]=='cover'
def expand(C,P):
    global best,nodes,timed_out
    nodes+=1
    if COVER:
        have=set(V[i][0] for i in C if i>=0)
        miss=[c for c in range(R+1) if c not in have]
        if len(miss)>target-len(C): return
        for c in miss:
            if not (VAL[c]&P): return
        real=[i for i in C if i>=0]
        dup=len(real)-len(have); lim=target-(R+1)
        if dup>lim: return
        if dup==lim:
            for c in have: P&=~VAL[c]
            if not P: return
    if nodes%2000==0 and time.time()-start>tlim: timed_out=True; return
    order=colour_sort(P)
    for v,c in reversed(order):
        if len(C)+c<=len(best): return
        C2=C+[v]
        P2=P&nb[v]
        if P2: expand(C2,P2)
        elif len(C2)>len(best):
            best=C2
        if timed_out: return
        if len(best)>=target: return
        P&=~(1<<v)
# symmetry/translation: WLOG the clique contains a vector with first coordinate 0 (compression) -- we simply search all.
if len(sys.argv)>7 and sys.argv[7]=='forceR':
    # every compressed family not inside the smaller box uses value R in some coordinate; by S_w symmetry, coordinate 0
    P=(1<<N)-1
    S=[i for i in range(N) if V[i][0]==R]
    lo=int(sys.argv[8]) if len(sys.argv)>8 else 0; hi=int(sys.argv[9]) if len(sys.argv)>9 else len(S)
    for v in S[:lo]: P&=~(1<<v)
    done_upto=lo
    for v in S[lo:hi]:
        if timed_out or len(best)>=target: break
        expand([v], P&nb[v])
        P&=~(1<<v)
        if not timed_out: done_upto+=1
    print('S_total',len(S),'completed_range',lo,done_upto)
else:
    expand([], (1<<N)-1)
print(json.dumps({'k':k,'w':w,'R':R,'N':N,'avgdeg':sum(deg)/N,'best_size':len(best),'best':[V[i] for i in best if i>=0],'nodes':nodes,'timed_out':timed_out,'secs':round(time.time()-start,1)}))

# Exact DP for A(sigma)=|R(sigma)| - sum_v d_B(v) over all sigma in S_n (Elder Conj. path1, arXiv:2201.12887).
# N(s)=#reduced words; B(s)=#(word,position) pairs where positions j,j+1,j+2 read i,i+1,i or i+1,i,i+1.
# Sum_v d_B(v) = B(s) since each braid factor occurrence gives a distinct neighbour (an edge counted once at each end).
# Recurrence over the last letter: B(s)=sum_{k in D_R(s)} B(s s_k) + 2*sum_{k: k,k+1 in D_R(s)} N(s w0_{k,k+1}).
import sys, itertools
n=int(sys.argv[1])
def act(p,k):  # right multiplication by s_k swaps positions k,k+1 (0-based)
    q=list(p); q[k],q[k+1]=q[k+1],q[k]; return tuple(q)
perms=sorted(itertools.permutations(range(n)), key=lambda p: sum(1 for a in range(n) for b in range(a+1,n) if p[a]>p[b]))
N={}; B={}
idp=tuple(range(n)); N[idp]=1; B[idp]=0
worst=None; cnt_neg=0; cnt_zero=0
for p in perms:
    if p==idp: continue
    D=[k for k in range(n-1) if p[k]>p[k+1]]
    nn=0; bb=0
    for k in D:
        q=act(p,k); nn+=N[q]; bb+=B[q]
    for k in D:
        if k+1 in D:
            u=act(act(act(p,k),k+1),k)
            bb+=2*N[u]
    N[p]=nn; B[p]=bb
    A=nn-bb
    if A<0: cnt_neg+=1
    if A==0: cnt_zero+=1
    r=bb/nn
    if worst is None or r>worst[0]: worst=(r,p,nn,bb)
print('n',n,'perms',len(perms),'A<0:',cnt_neg,'A=0:',cnt_zero,'max B/N',worst[0],'at',worst[1],'N',worst[2],'B',worst[3])
w0=tuple(range(n-1,-1,-1)); print('w0 N',N[w0],'B',B[w0])

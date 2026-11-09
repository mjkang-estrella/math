import sys; sys.path.insert(0,sys.argv[1]); from srg_lib import *
C6=from_edges(6,[(i,(i+1)%6) for i in range(6)]); print('C6',show(6,srg(6,C6)))
C5=from_edges(5,[(i,(i+1)%5) for i in range(5)]); print('C5',show(5,srg(5,C5)))
T=from_edges(5,[(0,1),(1,2),(1,3),(3,4)]); print('tree',show(5,srg(5,T)))
K33=from_edges(6,[(a,b) for a in range(3) for b in range(3,6)]); print('K33',show(6,srg(6,K33)))
# Figure 5 family G_r, r=4
r=4; idx={}
names=[]
for i in range(r+1):
    for c in 'abc': idx[c+str(i)]=len(idx)
idx['x']=len(idx); E=[]
for i in range(r+1): E+= [(idx['a%d'%i],idx['b%d'%i]),(idx['b%d'%i],idx['c%d'%i])]
for i in range(1,r+1): E+=[(idx['a%d'%i],idx['a0']),(idx['b%d'%i],idx['b0']),(idx['c%d'%i],idx['c0'])]
E+=[(idx['x'],idx['a0']),(idx['x'],idx['c0'])]
n=len(idx); inv={v:k for k,v in idx.items()}
s=show(n,srg(n,from_edges(n,E))); print('G4',{inv[u]:[inv[v] for v in w] for u,w in s.items()})

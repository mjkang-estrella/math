# Independent literal check of Definition 7.1 for the n=6 witness: nondecreasing chains with repeats,
# explicit permutations, k<=4; plus exact Farkas certificate for non-embeddability in the forced order.
import itertools
R={(2,3):0,(3,4):1,(1,2):2,(2,4):3,(0,1):4,(1,3):5,(1,4):6,(4,5):7,(3,5):8,(0,2):9,(2,5):10,(0,3):11,(0,4):12,(1,5):13,(0,5):14}
def D(x,y): return 0 if x==y else R[(min(x,y),max(x,y))]+1
viol=0; checked=0
for k in range(1,5):
    ch=[c for c in itertools.combinations_with_replacement(range(6),k+1)]
    perms=list(itertools.permutations(range(k)))
    for I in ch:
        pI=[D(I[l],I[l+1]) for l in range(k)]
        for J in ch:
            pJ=[D(J[l],J[l+1]) for l in range(k)]
            prec=any(all(pI[l]<=pJ[p[l]] for l in range(k)) and not all(pI[l]==pJ[p[l]] for l in range(k)) for p in perms)
            sim=any(all(pI[l]==pJ[p[l]] for l in range(k)) for p in perms)
            checked+=1
            if prec and not D(I[0],I[k])<D(J[0],J[k]): viol+=1
            if sim and not D(I[0],I[k])==D(J[0],J[k]): viol+=1
print('literal chain pairs checked (k<=4):',checked,'violations:',viol)
g=lambda a,b: [1 if a<=i<b else 0 for i in range(5)]
cert=[((2,3),(3,4)),((1,2),(2,4)),((0,1),(1,3)),((1,4),(4,5)),((3,5),(0,2))]
for lo,hi in cert: assert D(*lo)<D(*hi)
tot=[0]*5
for lo,hi in cert:
    for i,(a,b) in enumerate(zip(g(*hi),g(*lo))): tot[i]+=a-b
print('Farkas sum of (larger - smaller) gap vectors:',tot,'(all zero => 0 < 0 in forced order)')
print('distance-from-0 ranks', [D(0,x) for x in range(6)], 'max pair (0,5) =',D(0,5),'max =',max(D(a,b) for a in range(6) for b in range(6)))

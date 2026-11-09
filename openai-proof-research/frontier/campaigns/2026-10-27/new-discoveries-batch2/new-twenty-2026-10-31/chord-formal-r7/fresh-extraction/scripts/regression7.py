from pathlib import Path
import json

def data(n,mask):
    size=2*n
    mate=[i+3 if i<3 else i-3 if i<6 else i+1 if i%2==0 else i-1 for i in range(size)]
    rot=[]; flip=[]
    for i in range(size):
        rot.extend([3*i+j for j in ([2,0,1] if mask>>i&1 else [1,2,0])])
        flip.extend([3*((i-1)%size)+1,3*((i+1)%size),3*mate[i]+2])
    face=[rot[j] for j in flip]
    labels=[-1]*len(face); count=0
    for i in range(len(face)):
        if labels[i]<0:
            x=i
            while labels[x]<0:
                labels[x]=count; x=face[x]
            count+=1
    return face,count,labels[0]==labels[6*n-2]

checks=0; opposite=0
for n in range(3,8):
    for mask in range(1<<(2*n)):
        ff,old,same=data(n,mask)
        for p in range(2):
            for q in range(2):
                face,new,ns=data(n+1,mask+(p<<(2*n))+(q<<(2*n+1)))
                assert face[0]==6*n+(3 if q else 5)
                assert face[6*n-2]==6*n+(2 if p else 1)
                assert face[6*n+1]==6*n+(5 if q else 4)
                assert face[6*n+2]==6*n+(4 if q else 3)
                assert face[6*n+3]==6*n+(0 if p else 2)
                assert face[6*n+5]==6*n+(1 if p else 0)
                if p==q:
                    assert new==old+1 and ns==same
                else:
                    assert ns and new==old+(1 if same else -1)
                    opposite+=1
                fu,fv=ff[0],ff[6*n-2]
                if p==q==0:
                    targets=[fu,fv,6*n,6*n,fv,fu]; ranks=[1,2,0,1,1,2]; rep=2
                elif p==q==1:
                    targets=[fu,6*n,fv,fu,fv,6*n]; ranks=[1,1,2,2,1,0]; rep=5
                elif p==0:
                    targets=[fu,fu,fv,fv,fv,fu]; ranks=[1,3,2,3,1,2]; rep=None
                else:
                    targets=[fu,fv,fu,fu,fv,fv]; ranks=[1,2,3,2,1,3]; rep=None
                rr=list(range(6*n))+targets; rank=[0]*(6*n)+ranks
                small=ff+([6*n] if rep is not None else [])
                if rep is None: small[0],small[6*n-2]=small[6*n-2],small[0]
                embed=lambda x: x if x<6*n else 6*n+rep
                for x in range(len(small)): assert rr[face[embed(x)]]==small[x]
                for y in range(len(face)):
                    if y!=embed(rr[y]):
                        assert rr[face[y]]==rr[y] and rank[face[y]]<rank[y]
                checks+=1
out={'assignment_extensions':checks,'opposite_connectivity':opposite,'violations':0,'numerical_only':True}
Path('regression7.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)

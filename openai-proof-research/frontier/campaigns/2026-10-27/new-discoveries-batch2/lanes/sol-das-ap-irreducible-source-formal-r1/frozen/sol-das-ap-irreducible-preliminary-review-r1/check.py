"""Independent exact checker, standard library only; run through the assigned guard."""
import json
from pathlib import Path

def sc(a):
    n=len(a)
    def reach(transpose):
        seen={0}; todo=[0]
        while todo:
            i=todo.pop()
            for j in range(n):
                if (a[j][i] if transpose else a[i][j]) and j not in seen:
                    seen.add(j); todo.append(j)
        return len(seen)==n
    return reach(False) and reach(True)

def bmat(a):
    # A-minus retains NEGATIVE entries. Its subtraction cannot cancel a plus.
    return [[int(a[i][j]>0)+int(a[j][i]<0) for j in range(len(a))] for i in range(len(a))]

def ap(a):
    n=len(a)
    return (all(any(v>0 for v in row) for row in a)
            and all(any(a[i][j]>0 for i in range(n)) for j in range(n))
            and sc(a) and sc(bmat(a)))

def family(n):
    a=[[0]*n for _ in range(n)]
    for i,j in [(0,1),(1,0),(2,3),(3,2)]+[(0,k) for k in range(4,n)]+[(k,2) for k in range(4,n)]:
        assert a[i][j]==0; a[i][j]=1
    path=[3]+list(range(n-1,3,-1))+[1]
    for i,j in zip(path,path[1:]):
        assert a[i][j]==a[j][i]==0; a[i][j]=a[j][i]=-1
    return a,path

def test(a):
    assert ap(a)
    deleted=[]
    for i in range(len(a)):
        for j in range(len(a)):
            v=a[i][j]
            if not v: continue
            a[i][j]=0
            faults=[]
            if not all(any(x>0 for x in r) for r in a): faults.append('positive row')
            if not all(any(a[k][l]>0 for k in range(len(a))) for l in range(len(a))): faults.append('positive column')
            if not sc(a): faults.append('A reducible')
            if not sc(bmat(a)): faults.append('B reducible')
            assert not ap(a) and faults
            a[i][j]=v
            deleted.append({'cell_1based':[i+1,j+1],'sign':v,'failed':faults})
    return deleted

def main():
    # Literal matrix entered independently of the family generator.
    witness=[[0,1,0,0,1],[1,0,0,0,-1],[0,0,0,1,0],[0,0,1,0,-1],[0,-1,1,-1,0]]
    deletions=test(witness)
    assert len(deletions)==10>2*5-2
    assert family(5)[0]==witness
    results=[]
    for n in range(4,41):
        a,path=family(n); ds=test(a)
        assert len(ds)==4*n-10 and all(a[i][i]==0 for i in range(n))
        for t in range(len(path)-1):
            u={2,*path[:t+1]}
            out=[(i,j) for i in u for j in range(n) if j not in u and a[i][j]]
            assert out==[(path[t],path[t+1])]
        results.append({'n':n,'nonzeros':len(ds),'violates':len(ds)>2*n-2})
    # Explicit overlap control: plus(i,j) and minus(j,i) add, not cancel.
    assert bmat([[0,1],[-1,0]])[0][1]==2
    out={'literal_n5':witness,'deletions':deletions,'family_checks':results,
         'scope':'exact finite verification n=4..40, not proof of all n or any extremal optimum'}
    Path(__file__).with_name('check-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: literal n5, every deletion, family n4..40, outgoing cuts, signed overlap')

if __name__=='__main__': main()

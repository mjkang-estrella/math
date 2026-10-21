from graded_boundary import *
def words(length,k,N,prefix=''):
    if not length:
        if k==1:yield prefix
        return
    if k<N:yield from words(length-1,k+1,N,prefix+'M')
    if k>1:yield from words(length-1,k-1,N,prefix+'D')
def run():
    rows=[]
    for N in (3,4):
        xs=tuple(map(F,(2,3,5,7)[:N]))
        for n in (3,4,5):
            for word in words(2*n,1,N):
                for q in (F(1),F(2),F(1,2)):
                    a=trace(word,1,'color',xs,q);b=trace(word,1,'tableau',xs,q)
                    rows.append(dict(N=N,q=str(q),word=word,color=str(a),tableau=str(b),equal=a==b))
    (ROOT/'notes/variable-boundary-diagnostics.json').write_text(json.dumps(rows,indent=2)+'\n')
    bad=[r for r in rows if not r['equal']]
    print(json.dumps(dict(tests=len(rows),mismatches=len(bad),first_mismatches=bad[:8]),indent=2))
if __name__=='__main__':run()

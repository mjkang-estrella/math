# Disjoint Golomb rulers (Xu-Xiu-Fan-Liang arXiv:2409.14409): regular (I,J,IJ)-DGR = partition of {1..IJ} into I Golomb J-sets.
import sys,itertools,time
def golomb(S):
    d=set()
    for a,b in itertools.combinations(sorted(S),2):
        if b-a in d: return False
        d.add(b-a)
    return True
def rulers_containing(x,avail,J):
    # Golomb J-subsets of avail (sorted list) with minimum element x
    rest=[y for y in avail if y>x]
    out=[]
    def rec(cur,diffs,start):
        if len(cur)==J: out.append(tuple(cur)); return
        for idx in range(start,len(rest)):
            y=rest[idx]; nd=[y-c for c in cur]
            if any(t in diffs for t in nd) or len(set(nd))<len(nd): continue
            rec(cur+[y],diffs|set(nd),idx+1)
    rec([x],set(),0)
    return out
def partition(avail,J,limit=None):
    # exact cover of the set avail by Golomb J-sets; returns one solution or None
    avail=sorted(avail)
    if not avail: return []
    if len(avail)%J: return None
    x=avail[0]
    for R in rulers_containing(x,avail,J):
        rem=[y for y in avail if y not in R]
        s=partition(rem,J)
        if s is not None: return [R]+s
    return None
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='regular':
        Jmax=int(sys.argv[2]); Imax=int(sys.argv[3])
        for J in range(3,Jmax+1):
            row=[]
            for I in range(1,Imax+1):
                t=time.time(); s=partition(list(range(1,I*J+1)),J)
                row.append((I,s is not None)); print('J',J,'I',I,'regular' if s else 'NOT regular',s if s else '', '%.1fs'%(time.time()-t),flush=True)
    elif mode=='extend':
        J=int(sys.argv[2]); I=int(sys.argv[3])  # assumes H(I,J)=IJ; test every Golomb J-subset A1 of [(I+1)J]
        N=(I+1)*J; bad=[]; cnt=0
        for A in itertools.combinations(range(1,N+1),J):
            if not golomb(A): continue
            cnt+=1
            rem=[y for y in range(1,N+1) if y not in A]
            if partition(rem,J) is None: bad.append(A); print('NO EXTENSION',A,flush=True)
        print('J',J,'I',I,'N',N,'golomb A1 tested',cnt,'failures',len(bad))

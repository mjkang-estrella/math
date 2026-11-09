# Build Lean certificate data from the frozen matrix. Usage: python3 -I make_certificates.py <cex20_certificate.json> <verify_from_scratch.json> <out.json>
import json, sys, itertools
p=19; n=20; k=10
W=json.load(open(sys.argv[1]))['W']; V=json.load(open(sys.argv[2]))
word=V['min_word']; assert sum(1 for x in word if x)==9
Wm=[[x%p for x in r] for r in W]
def solve_rows(target, rows):
    # find coefficients c (len(rows)) with sum c_i rows_i = target mod p
    m=len(rows); M=[[rows[i][j] for i in range(m)]+[target[j]] for j in range(n)]
    r=0; piv=[]
    for c in range(m):
        pr=next((i for i in range(r,n) if M[i][c]%p),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; iv=pow(M[r][c],p-2,p); M[r]=[x*iv%p for x in M[r]]
        for i in range(n):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    assert all(M[i][-1]==0 for i in range(r,n))
    x=[0]*m
    for i,c in enumerate(piv): x[c]=M[i][-1]
    assert [sum(x[i]*rows[i][j] for i in range(m))%p for j in range(n)]==[t%p for t in target]
    return x
coeff=solve_rows(word, Wm)                     # word = sum coeff_i * row_i  (all 20 rows allowed)
R=list(range(k)); Cc=list(range(k))           # rows 0..9, columns 0..9
A=[[Wm[r][c] for c in Cc] for r in R]
def inv(A):
    M=[r[:]+[int(i==j) for j in range(k)] for i,r in enumerate(A)]
    for c in range(k):
        pr=next(i for i in range(c,k) if M[i][c]); M[c],M[pr]=M[pr],M[c]
        iv=pow(M[c][c],p-2,p); M[c]=[x*iv%p for x in M[c]]
        for i in range(k):
            if i!=c and M[i][c]: f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[c])]
    return [r[k:] for r in M]
B=inv(A)
mm=lambda X,Y:[[sum(X[i][t]*Y[t][j] for t in range(len(Y)))%p for j in range(len(Y[0]))] for i in range(len(X))]
I=[[int(i==j) for j in range(k)] for i in range(k)]
assert mm(A,B)==I and mm(B,A)==I
D=[solve_rows(Wm[r], [Wm[t] for t in R]) for r in range(n)]   # row r = sum_t D[r][t] row_t
json.dump({'W':W,'word':word,'coeff':coeff,'A':A,'B':B,'D':D},open(sys.argv[3],'w'))
print('coeff',coeff); print('word',word)

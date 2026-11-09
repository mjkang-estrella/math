# Independent exact verification of the order-20 counterexample (pure Python ints, no numpy).
import json
m=5;p=19;n=20
a,b,c,d=json.load(open('cex_20.json'))['seqs']
def circ(r): return [[r[(j-i)%m] for j in range(m)] for i in range(m)]
def mul(X,Y): return [[sum(X[i][k]*Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
def T(X): return [list(r) for r in zip(*X)]
def neg(X): return [[-x for x in r] for r in X]
R=[[1 if i+j==m-1 else 0 for j in range(m)] for i in range(m)]
A,B,C,D=map(circ,(a,b,c,d))
blocks=[[A,mul(B,R),mul(C,R),mul(D,R)],[neg(mul(B,R)),A,mul(T(D),R),neg(mul(T(C),R))],
        [neg(mul(C,R)),neg(mul(T(D),R)),A,mul(T(B),R)],[neg(mul(D,R)),mul(T(C),R),neg(mul(T(B),R)),A]]
H=[sum((blocks[I][J][i] for J in range(4)),[]) for I in range(4) for i in range(m)]
W=[[H[i][j]-(1 if i==j else 0) for j in range(n)] for i in range(n)]
assert all(W[i][i]==0 for i in range(n)) and all(W[i][j] in (1,-1) for i in range(n) for j in range(n) if i!=j)
WWt=mul(W,T(W)); assert all(WWt[i][j]==(19 if i==j else 0) for i in range(n) for j in range(n))
print('conference matrix order 20 verified; skew:',all(W[i][j]==-W[j][i] for i in range(n) for j in range(n)))
# find explicit integer combination of rows of W giving a low weight word mod 19 (solve directly)
# brute: Gaussian elimination over F_19 to express target word
word=json.load(open('cex_20.json'))['word']
# solve x^T W = word (mod p)
M=[[W[i][j]%p for i in range(n)]+[word[j]%p] for j in range(n)]  # n eqs (columns j), n unknowns x_i
rows=len(M); cols=n; r=0; piv=[]
for col in range(cols):
    pr=next((i for i in range(r,rows) if M[i][col]%p),None)
    if pr is None: continue
    M[r],M[pr]=M[pr],M[r]; inv=pow(M[r][col],p-2,p); M[r]=[(x*inv)%p for x in M[r]]
    for i in range(rows):
        if i!=r and M[i][col]:
            f=M[i][col]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
    piv.append(col); r+=1
assert all(M[i][-1]==0 for i in range(r,rows)), 'inconsistent'
x=[0]*n
for i,col in enumerate(piv): x[col]=M[i][-1]
w=[sum(x[i]*W[i][j] for i in range(n))%p for j in range(n)]
assert w==[v%p for v in word]
wt=sum(1 for v in w if v); print('row coefficients x =',x); print('codeword =',w,'weight',wt)
json.dump({'W':W,'x':x,'word':w,'weight':wt},open('cex20_certificate.json','w'))

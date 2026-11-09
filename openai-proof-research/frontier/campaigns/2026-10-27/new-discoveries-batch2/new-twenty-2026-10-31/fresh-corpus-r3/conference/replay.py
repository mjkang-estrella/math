# Independent pure-Python replay (no numpy): rebuild W from the Goethals–Seidel sequences, check the
# conference property, check the Lean data (W rows, coefficients, word, rank certificate) agree, and
# recheck weight-9 codeword and rank-10 certificate mod 19.
import json, re
m=5; p=19; n=20
a,b,c,d=json.load(open('cex_20.json'))['seqs']
circ=lambda r:[[r[(j-i)%m] for j in range(m)] for i in range(m)]
mul=lambda X,Y:[[sum(X[i][k]*Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
T=lambda X:[list(r) for r in zip(*X)]; neg=lambda X:[[-x for x in r] for r in X]
R=[[int(i+j==m-1) for j in range(m)] for i in range(m)]
A,B,C,D=map(circ,(a,b,c,d))
bl=[[A,mul(B,R),mul(C,R),mul(D,R)],[neg(mul(B,R)),A,mul(T(D),R),neg(mul(T(C),R))],[neg(mul(C,R)),neg(mul(T(D),R)),A,mul(T(B),R)],[neg(mul(D,R)),mul(T(C),R),neg(mul(T(B),R)),A]]
W=[sum((bl[I][J][i] for J in range(4)),[]) for I in range(4) for i in range(m)]
W=[[W[i][j]-(i==j) for j in range(n)] for i in range(n)]
assert all(W[i][j] in (0,1,-1) for i in range(n) for j in range(n))
assert all(sum(1 for j in range(n) if W[i][j])==19 and sum(1 for k in range(n) if W[k][i])==19 for i in range(n))
assert mul(W,T(W))==[[19*(i==j) for j in range(n)] for i in range(n)]
cert=json.load(open('cex20_certificate_w9.json')); assert cert['W']==W
x,word=cert['x'],cert['word']
assert [sum(x[i]*W[i][j] for i in range(n))%p for j in range(n)]==word and sum(1 for v in word if v)==9
rc=json.load(open('rank_certificate.json'))
Am=[[W[r][cc]%p for cc in rc['Cc']] for r in rc['R']]
I10=[[int(i==j) for j in range(10)] for i in range(10)]
assert [[v%p for v in r] for r in mul(Am,rc['B'])]==I10 and [[v%p for v in r] for r in mul(rc['B'],Am)]==I10
for r in range(n): assert [sum(rc['D'][r][t]*W[rc['R'][t]][j] for t in range(10))%p for j in range(n)]==[v%p for v in W[r]]
# Lean file carries the same data
src=open('lean/ConferenceMDSCounterexample.lean').read()
rows=re.search(r'def Wrows : List \(List ℤ\) := \[(.*?)\]\n\ndef W20',src,re.S).group(1)
assert json.loads('['+rows+']')==W
print('replay OK: conference matrix order 20 (skew), F19 code dim 10, weight-9 word; Lean data matches')

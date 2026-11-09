# Certificate that rowCode(W20) over F_19 has dimension exactly 10:
# rows R independent (10x10 minor on columns Cc invertible, with explicit inverse) and every row
# of W20 is an explicit F_19-combination of rows R.
import json, itertools
p=19; c=json.load(open('cex20_certificate.json')); W=[[e%p for e in r] for r in c['W']]; n=20
def inv_mat(A):
    k=len(A); M=[r[:]+[1 if i==j else 0 for j in range(k)] for i,r in enumerate(A)]
    for col in range(k):
        pr=next((i for i in range(col,k) if M[i][col]),None)
        if pr is None: return None
        M[col],M[pr]=M[pr],M[col]; iv=pow(M[col][col],p-2,p); M[col]=[x*iv%p for x in M[col]]
        for i in range(k):
            if i!=col and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[col])]
    return [r[k:] for r in M]
def mm(A,B): return [[sum(A[i][t]*B[t][j] for t in range(len(B)))%p for j in range(len(B[0]))] for i in range(len(A))]
# greedy row basis
R=[]; 
def rank(rows):
    M=[r[:] for r in rows]; rk=0
    for col in range(n):
        pr=next((i for i in range(rk,len(M)) if M[i][col]),None)
        if pr is None: continue
        M[rk],M[pr]=M[pr],M[rk]; iv=pow(M[rk][col],p-2,p); M[rk]=[x*iv%p for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
for i in range(n):
    if rank([W[j] for j in R+[i]])==len(R)+1: R.append(i)
print('rank',len(R),'rows',R)
for Cc in itertools.combinations(range(n),len(R)):
    A=[[W[r][cc] for cc in Cc] for r in R]; B=inv_mat(A)
    if B: break
Cc=list(Cc); assert mm(A,B)==[[int(i==j) for j in range(10)] for i in range(10)] and mm(B,A)==[[int(i==j) for j in range(10)] for i in range(10)]
# D: row r = sum_t D[r][t] * W[R[t]] ; D[r] = (W[r] restricted to Cc) * B
D=[mm([[W[r][cc] for cc in Cc]],B)[0] for r in range(n)]
for r in range(n): assert [sum(D[r][t]*W[R[t]][j] for t in range(10))%p for j in range(n)]==W[r]
print('cols',Cc)
json.dump({'R':R,'Cc':Cc,'A':A,'B':B,'D':D},open('rank_certificate.json','w'))

# MathDB 349179 / Liu-Chew-Heule Conjecture 11: for prime k, verify the affine-plane coloring
# chi((a,i),(b,j)) = (j - i - a*b) mod k of G_{k^2,k^2} (row = a*k+i, column = b*k+j):
# (1) right shift pattern in every k-subgrid, (2) each color exactly k times per subgrid, (3) rectangle-free.
# Also checks composite k (where the conjecture makes no claim) to see where the formula fails.
import sys
def check(k):
    n=k*k
    col=[[((j%k)-(i%k)-(i//k)*(j//k))%k for j in range(n)] for i in range(n)]
    for a in range(k):
        for b in range(k):
            cnt=[0]*k
            for i in range(k):
                for j in range(k):
                    c=col[a*k+i][b*k+j]; cnt[c]+=1
                    if col[a*k+(i+1)%k][b*k+(j+1)%k]!=c: return 'shift-fail'
            if cnt!=[k]*k: return 'balance-fail'
    # rectangle-free: for each pair of rows, no color shared in two columns
    for r1 in range(n):
        R1=col[r1]
        for r2 in range(r1+1,n):
            R2=col[r2]; seen=set()
            for j in range(n):
                if R1[j]==R2[j]:
                    if R1[j] in seen: return 'rectangle(%d,%d)'%(r1,r2)
                    seen.add(R1[j])
    return 'ok'
for k in [int(x) for x in sys.argv[1:]]:
    print(k,check(k),flush=True)

import json, math, itertools
from pathlib import Path
P=Path(__file__).resolve().parent
N=500
C=[[1]*(N+1) for _ in range(N+1)]
rows=[]
for n in range(1,N+1):
    coeff=[math.comb(n-1,k-1) for k in range(1,n+1)]
    for l in range(n):
        C[n][l]=sum(coeff[k-1]*min(l+1,k)*C[k-1][l]*C[n-k][l] for k in range(1,n+1))
    for l in range(n,N+1): C[n][l]=C[n][n-1]
    a=[C[n][l]-(C[n][l-1] if l else 0) for l in range(n)]
    assert sum(a)==(n+1)**(n-1)
    rows.append(a)
# independent literal parking exhaustive n<=6: failed preferences simply discarded
brute=[]
for n in range(1,7):
    a=[0]*n
    for w in itertools.product(range(1,n+1),repeat=n):
        occ=set();m=0
        for x in w:
            s=x
            while s in occ:s+=1
            if s>n:break
            occ.add(s);m=max(m,s-x)
        else:a[m]+=1
    assert a==rows[n-1]
    brute.append(a)
viol=[];lc=[];tp=[]
for n,a in enumerate(rows,1):
    down=False
    for j in range(1,n):
        if a[j]<a[j-1]:down=True
        if down and a[j]>a[j-1]:viol.append([n,j])
    for j in range(1,n-1):
        if a[j]**2<a[j-1]*a[j+1]:lc.append([n,j])
    if n>1:
        b=rows[n-2]
        for j in range(len(b)-1):
            if a[j+1]*b[j]<a[j]*b[j+1]:tp.append([n,j])
out={'N':N,'literal_brute_rows':brute,'source_table_rows_1_to_9':rows[:9],
'unimodality_failures':viol,'logconcavity_failures':lc[:10],
'adjacent_size_likelihood_ratio_failures':tp[:10],
'modes':[[n,[j for j,x in enumerate(a) if x==max(a)]] for n,a in enumerate(rows,1)]}
(P/'check-large-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['modes','source_table_rows_1_to_9']}))

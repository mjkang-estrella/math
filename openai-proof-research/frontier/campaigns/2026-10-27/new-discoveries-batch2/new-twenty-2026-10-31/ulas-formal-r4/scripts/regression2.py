import json

def cm(m,N):
    a=[1]+[0]*(N-1)
    for _ in range(m):
        for step in [1]+[2**i for i in range(N.bit_length())]:
            for n in range(step,N): a[n]+=a[n-step]
    return a

def mul(a,b,N):
    out=[0]*N
    for i in range(min(len(a),N)):
        for j in range(min(len(b),N-i)): out[i+j]+=a[i]*b[j]
    return out

N=256
checks=0
for m in range(25):
    a=cm(m,N)
    w=[1]+[2]*(N-1)
    wm=[1]+[0]*(N-1)
    for _ in range(m): wm=mul(wm,w,N)
    exp=[a[n//2] if n%2==0 else 0 for n in range(N)]
    assert mul(wm,exp,N)==a
    assert all(x%2==0 for x in a[1:])
    assert 3*(a[4]-a[1])==2*m*m*(m+1)*(m+5)
    A=[[1]+[0]*(N-1)]
    for j in range(4):
        t=mul(wm,A[-1],len(A[-1]));A.append(t[::2])
    for j in range(3):
        L=len(A[j+2]);d=[A[j+2][i]-A[j][i] for i in range(L)]
        read=mul(a,d,L)
        for n in range(L):
            assert read[n]==a[4*2**j*n]-a[2**j*n]
            checks+=1
print(json.dumps({'status':'PASS','m_range':[0,24],'series_length':N,'general_j_readout_pairs':checks,'functional_equation':True,'parity':True,'universal_low_polynomial':True}))

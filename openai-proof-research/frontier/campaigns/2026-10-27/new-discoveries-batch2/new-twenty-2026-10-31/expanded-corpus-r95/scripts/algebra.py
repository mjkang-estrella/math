import pathlib,json,math,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parents[1]
N=310;S=[[0]*(N+1) for _ in range(N+1)];s=[[0]*(N+1) for _ in range(N+1)];S[0][0]=s[0][0]=1
for n in range(1,N+1):
 for k in range(1,n+1):S[n][k]=S[n-1][k-1]+k*S[n-1][k];s[n][k]=s[n-1][k-1]+(n-1)*s[n-1][k]
for j in range(1,101):
 seq=[sum(S[n][i]*s[i-1][n-j-1] for i in range(n-j,n+1)) for n in range(j+1,3*j+3)]
 coeff=[sum((-1)**i*math.comb(2*j+1,i)*seq[r-i] for i in range(r+1)) for r in range(2*j+2)]
 while coeff and coeff[-1]==0:coeff.pop()
 rec={'diagonal':j,'symmetric':coeff==coeff[::-1],'sum_correct':sum(coeff)==math.factorial(2*j)//math.factorial(j),'unimodal':all(coeff[i]<=coeff[i+1] for i in range(len(coeff)//2)),'coefficients':coeff}
 print(json.dumps(rec),flush=True)

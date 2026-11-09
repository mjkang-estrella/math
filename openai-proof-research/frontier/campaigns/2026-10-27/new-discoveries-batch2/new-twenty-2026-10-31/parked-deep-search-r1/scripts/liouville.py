import sys,pathlib,json,time
D=pathlib.Path(sys.argv[1]);N=int(sys.argv[2]);least=list(range(N+1))
for p in range(2,int(N**.5)+1):
 if least[p]==p:
  for j in range(p*p,N+1,p):
   if least[j]==j:least[j]=p
f=bytearray(N+1);f[1]=1
for n in range(2,N+1):f[n]=1-f[n//least[n]]
p=D/'outputs'/f'divine-liouville-{N}.txt';p.write_text(''.join('+' if x else '-' for x in f[1:])+'\n');print(p)

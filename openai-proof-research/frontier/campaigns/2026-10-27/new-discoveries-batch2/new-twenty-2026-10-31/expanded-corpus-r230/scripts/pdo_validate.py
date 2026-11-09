import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];N=24;P=[0]*(N+1);B=P[:];P[0]=1
for d in range(1,N+1,2):
 p=P[:];b=B[:]
 for s in range(N+1):
  for a in range(1,(N-s)//d+1):
   p[s+a*d]+=a*P[s];b[s+a*d]+=a*(B[s]+P[s])
 P,B=p,b
expected=json.loads((D/'pdo-6000.json').read_text())['initial']
assert B==expected,(B,expected)
print('Direct multiplicity-weighted designated-part enumeration agrees for all indices 0 through 24.')

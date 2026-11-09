import pathlib,ctypes,json,re,math,os
D=pathlib.Path(__file__).resolve().parents[1];lib=ctypes.CDLL(str(D/'scripts/compact-inversions.so'));clib=ctypes.CDLL(None)
p=D/'logs/compact-bruteforce-comparison.log'
with p.open('w') as f:
 old=os.dup(1);os.dup2(f.fileno(),1)
 for n in range(2,9):
  for k in range(3,n+1):assert lib.run(n,k)==0
 assert lib.run(12,2)==1
 clib.fflush(None);os.dup2(old,1);os.close(old)
ans=json.loads((D/'bruteforce-inversions.json').read_text());checks=0
for p in [D/'logs/compact-bruteforce-comparison.log',*sorted((D/'logs').glob('compact-22-24*.log'))]:
 ls=p.read_text().splitlines()
 for a,b in zip(ls[::2],ls[1::2]):
  n,k,deg=map(int,re.search(r'N (\d+) k (\d+) degree (\d+)',a).groups());c=list(map(int,a.split('coefficients ')[1].strip(',').split(',')))
  assert sum(c)==math.factorial(n);assert c==c[::-1];assert len(c)==deg+1
  z=next((z for z in ans if z['n']==n and z['k']==k),None)
  if z:assert z['coefficients']==c;checks+=1
print('compact matches brute force in',checks,'cases; factorial totals, reversal symmetry pass; k2 S12 negative control fails unimodality as expected')

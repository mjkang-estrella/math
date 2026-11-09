import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
p=1000000007
def trim(a):
 while a and a[-1]==0:a.pop()
 return a
def rem(a,b):
 a=a[:]
 while len(a)>=len(b):
  c=a[-1]*pow(b[-1],-1,p)%p;k=len(a)-len(b)
  for j,x in enumerate(b):a[j+k]=(a[j+k]-c*x)%p
  trim(a)
 return a
def gcd(a,b):
 while b:a,b=b,rem(a,b)
 return a
def der(a):return trim([i*a[i]%p for i in range(1,len(a))])
for f in sorted((D/'logs').glob('squares[0-9]*.log')):
 try:r=json.loads(f.read_text())
 except Exception:continue
 C=r['C'];G=gcd(C,der(C));H=gcd(G,der(G));r.update(gcd_derivative_degree=len(G)-1,triple_root_test_degree=len(H)-1)
 (D/f'outputs/{f.stem}.json').write_text(json.dumps(r,indent=2));r.pop('sequence');r['C_balanced']=[c if c<p//2 else c-p for c in C];r.pop('C');out.append(r);print({k:v for k,v in r.items() if k!='C_balanced'})
(D/'outputs/squares-summary.json').write_text(json.dumps(out,indent=2))

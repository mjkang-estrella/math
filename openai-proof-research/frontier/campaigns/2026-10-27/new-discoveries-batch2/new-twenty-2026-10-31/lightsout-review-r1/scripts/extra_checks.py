# Run check.py in this namespace; no imports of author code.
from pathlib import Path
exec((Path(__file__).parent/'check.py').read_text())
extra={'orders':[],'cross_pairs':[],'all_small_grids':[]}
for j in range(1,10):
 m=3**j;a=2;t=1
 while a!=1:a=a*2%m;t+=1
 assert t==2*3**(j-1) and pow(2,t//2,m)==m-1
 extra['orders'].append({'j':j,'order':t,'half_power':m-1})
for i in range(1,8):
 for j in range(1,8):
  p=1^(fib(3**(i-1))<<1);q=translate(1^(fib(3**(j-1))<<1));g=gcd(p,q);assert g==1
  extra['cross_pairs'].append({'i':i,'j':j,'gcd':g})
for n in range(1,21):
 d=grid(n);g=gcd(fib(n+1),translate(fib(n+1))).bit_length()-1;assert d==g
 extra['all_small_grids'].append({'n':n,'nullity':d,'gcd_degree':g})
(r/'logs/extra-checks.json').write_text(json.dumps(extra,indent=2));print('All orders, 49 cross-pairs, 20 direct grids passed.')

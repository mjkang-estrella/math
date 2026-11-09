from pathlib import Path
from math import comb
from gmpy2 import mpz
import json
D=Path(__file__).resolve().parents[1]
a=[mpz(sum(2*comb(n+1,k-1)*comb(n+1,k)*comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2)) for n in range(1,61)];rows=[]
for r in range(1,23):
 a=[a[i]*a[i+2]-a[i+1]**2 for i in range(len(a)-2)];row={'r':r,'n_range':[1,len(a)],'negative_indices':[i+1 for i,x in enumerate(a) if x<0],'largest_integer_bits':max(x.bit_length() for x in a)};rows.append(row);print(row,flush=True);(D/'outputs/baxter-gmp.json').write_text(json.dumps(rows,indent=2)+'\n')

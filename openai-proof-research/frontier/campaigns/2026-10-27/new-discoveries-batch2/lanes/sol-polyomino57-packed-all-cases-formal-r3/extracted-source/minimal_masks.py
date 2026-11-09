from generate_cases import *
rr=json.loads((L/'frozen/frozen/inputs/compression/verification.json').read_text())['receipts']
for r in rr:
 if r['verified']!='potential-inequalities':continue
 a,b,e,n,k=(r[t] for t in ['a','b','e','vertices','groups']);raw=gzip.decompress((L/f'frozen/frozen/inputs/compression/steiner-{a}-{b}-{e}.bin.gz').read_bytes())
 masks=[m for m in range(1,1<<k) if all(x>=12 for x in raw[m*n:(m+1)*n])];m=min(masks,key=lambda m:(m.bit_count(),m));print(a,b,e,k,m.bit_count(),m,flush=True)

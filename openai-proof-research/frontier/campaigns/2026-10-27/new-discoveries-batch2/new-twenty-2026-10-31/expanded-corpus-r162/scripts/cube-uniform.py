import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for d in [10,13,16]:
 m=d-1;H=1<<(m-1);M=d*(1<<m);z=2*((M+2)//6);C=M-z;delta=0 if m%2 else 2*d-4
 assert (C-delta-(1<<m))%2==0
 B=(C-delta-(1<<m))//2;r,b=divmod(B,m);q=1 if (m-b)%2==0 else 2;t=(q*m-b)//2
 assert H>=12*m and r>=H//2 and H-r>=3*m and 0<=t<=m
 even=[0] if q==1 else [0,15];zeros=[15,51] if delta else []
 neighbors=lambda x:{x^(1<<j) for j in range(m)}
 special=set().union(*(neighbors(x) for x in even));reserve=set().union(*(neighbors(x) for x in zeros)) if zeros else set()
 assert not special&reserve
 S=set(sorted(special)[:t])
 extra=[v for v in range(1<<m) if v.bit_count()%2 and v not in special|reserve]
 S.update(extra[:r-t]);assert len(S)==r
 ones=S|set(even)
 h=[int(v in ones) for v in range(1<<m)]
 cut=sum(h[v]!=h[v^(1<<j)] for v in range(1<<m) for j in range(m))//2;assert cut==B
 f=[(v>>m)^h[v% (1<<m)] for v in range(1<<d)]
 if delta:
  f[zeros[0]]^=1;f[(1<<m)+zeros[1]]^=1
 actual=sum(f[v]!=f[v^(1<<j)] for v in range(1<<d) for j in range(d))//2
 assert actual==C and sum(f)==1<<(d-1)
 row={'d':d,'m':m,'H':H,'M':M,'zero_edges':z,'crossing_edges':C,'B':B,'r':r,'b':b,'q':q,'t':t,'delta':delta,'direct_edge_recount':actual,'balanced':True}
 print(row,flush=True);out.append(row)
(D/'outputs/cube-uniform.json').write_text(json.dumps(out,indent=2))
# Exact arithmetic bound diagnostics far beyond the materialized examples.
for m in range(9,301,3):
 H=1<<(m-1);d=m+1;M=d*(1<<m);z=2*((M+2)//6);C=M-z;delta=0 if m%2 else 2*d-4
 B=(C-delta-(1<<m))//2;r,b=divmod(B,m)
 assert H>=12*m and r>=H//2 and H-r>=3*m
print('Integer bounds verified for all m divisible by 3 from 9 through 300; diagnostics only.')

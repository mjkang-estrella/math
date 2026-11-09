import pathlib,json,math,sys,time
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);g=sorted({x*(5*x+1)//2 for x in range(-math.isqrt(N)-1,math.isqrt(N)+2) if x*(5*x+1)//2<=N});mask=(1<<(N+1))-1
for weights,exc in [((1,1,1),[1,10,19,94]),((2,1,3),[1,5,32]),((2,4,1),[1,5,70]),((2,1,5),[1,5])]:
 A,B,C=[[w*v for v in g if w*v<=N] for w in weights];bits=sum(1<<v for v in A);pair=0
 for v in B:pair|=(bits<<v)&mask
 triple=0
 for v in C:triple|=(pair<<v)&mask
 missing=mask^triple;miss=[]
 while missing:
  z=missing&-missing;miss.append(z.bit_length()-1);missing-=z
 print(json.dumps(dict(N=N,weights=weights,missing=miss,expected=exc,all_match=miss==exc,variable_value_counts=[len(A),len(B),len(C)])),flush=True)

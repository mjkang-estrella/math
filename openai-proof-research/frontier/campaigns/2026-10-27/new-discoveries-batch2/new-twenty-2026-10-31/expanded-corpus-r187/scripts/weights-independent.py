import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];w=[0]*4;hist=[0]*5
for mask in range(1<<16):
 rows=[mask>>(4*i)&15 for i in range(4)];basis=[0]*4;rank=0
 for x in rows:
  while x:
   j=x.bit_length()-1
   if basis[j]:x^=basis[j]
   else:basis[j]=x;rank+=1;break
 hist[rank]+=1
 if rank<=2:
  trace=0
  for i in range(4):
   trace^=mask>>(5*i)&1;w[i]+=trace
print({'rank_histogram':hist,'weights_t2_q2_ell4_m4':w})
(D/'outputs/weights-independent.json').write_text(json.dumps({'rank_histogram':hist,'weights_t2_q2_ell4_m4':w}))

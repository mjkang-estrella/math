import pathlib,json,math,itertools,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186');counts={};violations=[]
for q in [123,132,231,321]:
 p=L/'logs'/('cycles18-123-fixed.log' if q==123 else f'cycles18-{q}.log');rows=[list(map(int,s.split())) for s in p.read_text().splitlines()];assert len(rows)==18
 counts[q]={n:c for _,n,t,c in rows}
 for _,n,t,c in rows:assert t==math.comb(2*n,n)//(n+1)
 for n in range(3,18):
  if not 2*counts[q][n]<=counts[q][n+1]<=4*counts[q][n]:violations.append([q,n])
# independent brute-force validation uses all permutations through n=8 and all triples
for n in range(1,9):
 brute={q:0 for q in counts}
 for p in itertools.permutations(range(n)):
  v=0
  for k in range(n):
   v=p[v]
   if v==0:break
  if k!=n-1 or v!=0:continue
  present=set()
  for i,j,k in itertools.combinations(range(n),3):
   a,b,c=p[i],p[j],p[k];t=[a,b,c];r=100*(1+(b<a)+(c<a))+10*(1+(a<b)+(c<b))+1+(a<c)+(b<c);present.add(r)
  for q in brute:
   if q not in present:brute[q]+=1
 for q in brute:assert brute[q]==counts[q][n],(q,n,brute[q],counts[q][n])
bs=json.loads((L/'outputs/bisection.json').read_text())
for r in bs:
 A=r['witness'];assert len(A)==r['maximum_nonempty_family'];assert all(2*(a&b).bit_count() in [a.bit_count(),b.bit_count()] for a,b in itertools.combinations(A,2))
out={'cycles':{'range':'n=1..18; four symmetry representatives covering six length-three patterns','catalan_count_check':True,'independent_factorial_check_through':8,'inequalities_checked_n':[3,17],'violations':violations,'counts':counts},'bisection_witness_validation':True}
(L/'outputs/validation.json').write_text(json.dumps(out,indent=2));print('validated cycles and bisection witnesses; violations',violations)

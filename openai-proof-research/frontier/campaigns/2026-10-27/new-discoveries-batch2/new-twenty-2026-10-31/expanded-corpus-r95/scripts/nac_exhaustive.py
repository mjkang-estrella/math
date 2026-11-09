import pathlib,itertools,json
L=pathlib.Path(__file__).resolve().parents[1];ns={};exec((L/'scripts/nac.py').read_text().split('for n in [6,7,8,9,10,11,12,14,16]:')[0],ns)
count=ns['count'];zero=ns['zero'];stable=ns['stable']
def prisms(n,es):
 E=set(es);tri=[t for t in itertools.combinations(range(n),3) if all(e in E for e in itertools.combinations(t,2))];found=set()
 for a,b in itertools.combinations(tri,2):
  if set(a)&set(b):continue
  for p in itertools.permutations(b):
   cross={tuple(sorted((x,y))) for x,y in zip(a,p)}
   if cross<=E:found.add(tuple(sorted(cross|set(itertools.combinations(a,2))|set(itertools.combinations(b,2)))))
 return len(found)
n=6;hist={};laman=0;bad=[]
for es in itertools.combinations(list(itertools.combinations(range(n),2)),2*n-3):
 if any(sum(mask>>a&1 and mask>>b&1 for a,b in es)>2*mask.bit_count()-3 for mask in range(1,1<<n) if mask.bit_count()>=2):continue
 laman+=1;c,nodes,complete=count(n,list(es));assert complete;hist[c]=hist.get(c,0)+1
 if c==1 and not zero(es,n) and (stable(n,es) or prisms(n,es)!=1):bad.append(es)
print(json.dumps({'n':n,'labeled_Laman_graphs':laman,'NAC_count_capped_2_hist':hist,'conjecture_failures':bad}),flush=True)
# Finish classification on the sampled unique graphs, including those beyond order 10.
for row in map(json.loads,(L/'logs/nac.txt').read_text().splitlines()):
 for v in row['unique']:
  if not v['one_open_zero_extension']:
   es=[tuple(e) for e in v['edges']];p=prisms(row['n'],es)
   print(json.dumps({'n':row['n'],'edges':es,'stable_cut':v['stable_cut_if_not_zero'],'prism_subgraphs':p,'meets_first_family':not v['stable_cut_if_not_zero'] and p==1}),flush=True)

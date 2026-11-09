import pathlib,itertools,collections,json
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');out=[]
for n in range(1,6):
 pairs=list(itertools.combinations(range(n),2));idx={p:i for i,p in enumerate(pairs)};maps=[[idx[tuple(sorted((p[u],p[v])))] for u,v in pairs] for p in itertools.permutations(range(n))];reps=[]
 for mask in range(1<<len(pairs)):
  selected=[i for i in range(len(pairs)) if mask>>i&1]
  if any(sum(1<<mp[i] for i in selected)<mask for mp in maps):continue
  reps.append([pairs[i] for i in selected])
 for q in [2,3,4]:
  types=list(itertools.combinations_with_replacement(range(q),2));ti={p:i for i,p in enumerate(types)};polys={};hits=[]
  for ri,edges in enumerate(reps):
   poly=collections.Counter()
   for a in itertools.product(range(q),repeat=n):
    exp=[0]*(q+len(types))
    for x in a:exp[x]+=1
    for u,v in edges:exp[q+ti[tuple(sorted((a[u],a[v])))]]+=1
    poly[tuple(exp)]+=1
   key=tuple(sorted(poly.items()))
   if key in polys:hits.append([polys[key],ri])
   polys[key]=ri
  row={'n':n,'q':q,'nonisomorphic_graphs':len(reps),'collisions':hits};out.append(row);print(row,flush=True)
(D/'outputs/hompoly.json').write_text(json.dumps(out,indent=2))

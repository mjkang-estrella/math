import itertools,pathlib,json,collections,time
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');out=[];start=time.monotonic()
for m,L in [(3,4),(3,5),(3,6),(3,7),(3,8),(4,4),(4,5)]:
 hist=collections.Counter();pairs=list(itertools.combinations(range(m),2))
 proj=[[((c>>i)&1)+2*((c>>j)&1) for c in range(1<<m)] for i,j in pairs]
 for cols in itertools.permutations(range(1<<m),L):
  count=0
  for p in proj:
   seen=0
   for c in cols:
    seen|=1<<p[c]
    if seen==15:count+=1;seen=0
  hist[count]+=1
 row={'m':m,'k':2,'columns':L,'ordered_simple_matrices':sum(hist.values()),'contribution_count_histogram':dict(hist),'minimum':min(hist),'maximum':max(hist)};out.append(row);print(row,time.monotonic()-start,flush=True)
(D/'outputs/matrices.json').write_text(json.dumps(out,indent=2))

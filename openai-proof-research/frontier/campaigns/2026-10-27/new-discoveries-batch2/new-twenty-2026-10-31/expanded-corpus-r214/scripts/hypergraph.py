import itertools,functools,json,pathlib,sys,random
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);k=int(sys.argv[2]);allE=list(itertools.combinations(range(n),k));pairs=list(itertools.combinations(range(n),2));em=[sum(1<<v for v in e) for e in allE];pm=[sum(1<<j for j,p in enumerate(pairs) if set(p)<=set(e)) for e in allE];fullpairs=(1<<len(pairs))-1
covered=0;tested=0;bad=[]
for mask in range(1<<len(allE)):
 if mask.bit_count()<2:continue
 tested+=1;idx=[j for j in range(len(allE)) if mask>>j&1];p=0
 for j in idx:p|=pm[j]
 if p!=fullpairs:continue
 covered+=1;es=[allE[j] for j in idx];full=(1<<len(es))-1
 def tour():
  for start in es[0]:
   @functools.lru_cache(None)
   def dfs(used,v):
    if used==full:return v==start
    for i,e in enumerate(es):
     if used>>i&1 or v not in e:continue
     for w in e:
      if w!=v and dfs(used|1<<i,w):return True
    return False
   if any(dfs(1,v) for v in es[0] if v!=start):return True
  return False
 if not tour():bad.append({'mask':mask,'edges':es});print('FAIL',bad[-1],flush=True);break
print(n,k,tested,covered,'failures',len(bad));(D/f'outputs/hyper-{n}-{k}.json').write_text(json.dumps(dict(n=n,k=k,tested=tested,covering=covered,bad=bad,scope='simple labelled k-uniform hypergraphs, all edge subsets with >=2 edges; exact closed edge-distinct walk DFS'),indent=2))

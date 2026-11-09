import pathlib,itertools,json,sys,time,functools,gzip,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
def partitions(n,cap,left):
 if n==0:yield ();return
 if left==0:return
 for k in range(min(n,cap),0,-1):
  for p in partitions(n-k,k,left-1):yield (k,)+p
@functools.lru_cache(None)
def test(seq):
 n=len(seq);I=[0]+list(itertools.accumulate(seq));tested=0
 for size in range(1,n*n):
  q,r=divmod(size,n);target=q*I[n]+I[r]+sum(I[q+(j<r)] for j in range(n))
  for rows in partitions(size,n,n):
   cols=[sum(x>j for x in rows) for j in range(n)]
   val=sum(I[x] for x in rows)+sum(I[x] for x in cols);tested+=1
   if val>target:return False,tested,{'size':size,'rows':rows,'value':val,'lex':target}
 return True,tested,None
out=[];total=0
atlas=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i25_matching_entropy_improvement/vendor/networkx/generators/atlas.dat.gz')
(D/'outputs/atlas-provenance.json').write_text(json.dumps({'path':str(atlas),'sha256':hashlib.sha256(atlas.read_bytes()).hexdigest()}))
for block in gzip.decompress(atlas.read_bytes()).decode().split('GRAPH ')[1:]:
 lines=block.strip().splitlines();gid=int(lines[0]);n=int(lines[1].split()[1]);G={i:[] for i in range(n)}
 for line in lines[2:]:
  u,v=map(int,line.split());G[u].append(v);G[v].append(u)
 if n<2 or n>int(sys.argv[1]) or len(set(map(len,G.values())))<2:continue
 total+=1;adj=[sum(1<<j for j in G[i]) for i in range(n)];e=[0]*(1<<n);best=[0]*(n+1)
 for s in range(1,1<<n):
  v=(s&-s).bit_length()-1;t=s^(1<<v);e[s]=e[t]+(adj[v]&t).bit_count();best[s.bit_count()]=max(best[s.bit_count()],e[s])
 # nested optimal order exists iff directed subset DAG has a full path
 reach={0}
 for k in range(1,n+1):reach={s for s in range(1<<n) if s.bit_count()==k and e[s]==best[k] and any(s^(1<<v) in reach for v in range(n) if s>>v&1)}
 if not reach:continue
 seq=tuple(best[i]-best[i-1] for i in range(1,n+1));ok,nt,w=test(seq)
 out.append({'graph6':str(gid),'n':n,'delta':seq,'square_lex_optimal':ok,'partitions_checked':nt,'obstruction':w})
(D/'outputs/eip-atlas.json').write_text(json.dumps({'nonregular_graphs':total,'nested_graphs':len(out),'delta_sequences':test.cache_info().currsize,'records':out},indent=2));print(total,len(out),test.cache_info());print('counterexamples',sum(r['square_lex_optimal'] for r in out))

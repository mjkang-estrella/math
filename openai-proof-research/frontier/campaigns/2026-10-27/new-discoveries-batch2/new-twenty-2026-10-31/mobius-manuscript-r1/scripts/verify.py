from pathlib import Path
import json,hashlib,zipfile,stat,shutil,random,math
D=Path(__file__).resolve().parents[1]; B=D.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
W={6:[17,13,7,8,3,15,6,18,4,5,12,2,10,1,9,16,14,11],4:[11,2,9,12,5,10,6,8,3,7,4,1]}
result={}
for n,l in W.items():
 edges=[(i,(i+1)%(2*n)) for i in range(2*n)]+[(i,i+n) for i in range(n)]
 assert len(set(tuple(sorted(e)) for e in edges))==3*n
 assert sorted(l)==list(range(1,3*n+1))
 sums=[sum(a for e,a in zip(edges,l) if v in e) for v in range(2*n)]
 assert all(sums[u]!=sums[v] for u,v in edges) and len(set(sums))==3
 cycle=list(range(n+1)); assert (n+1)%2==1
 pairs=[(sums[u],sums[v]) for u,v in edges]
 result[str(n)]={'order':2*n,'size':3*n,'labels':l,'sums':sums,'edge_color_pairs':pairs,'sum_labels':sum(l),'sum_vertex_sums':sum(sums),'colors':sorted(set(sums)),'classes':{str(x):sums.count(x) for x in sorted(set(sums))},'odd_cycle':cycle,'odd_cycle_length':n+1,'incident_labels':[[a for e,a in zip(edges,l) if v in e] for v in range(2*n)]}
# Fresh finite heuristic, no solver: minimize unequal within-class sums for a fixed proper 3-coloring.
search=[]
for n in [8,10]:
 edges=[(i,(i+1)%(2*n)) for i in range(2*n)]+[(i,i+n) for i in range(n)]
 rng=random.Random(339235+n)
 # Greedy proper coloring; all three classes nonempty.
 colors=[]
 for v in range(2*n):
  used={colors[u] for u in range(v) if (u,v) in edges or (v,u) in edges}; colors.append(next(c for c in range(3) if c not in used))
 def score(l):
  sums=[sum(a for e,a in zip(edges,l) if v in e) for v in range(2*n)]
  return sum((sums[u]-sums[v])**2 for u in range(2*n) for v in range(u) if colors[u]==colors[v])
 l=list(range(1,3*n+1)); rng.shuffle(l); cur=score(l); best=cur
 for step in range(20000):
  i,j=rng.sample(range(3*n),2); l[i],l[j]=l[j],l[i]; nxt=score(l)
  if nxt<=cur or rng.random()<math.exp(min(0,(cur-nxt)/max(1,40*(1-step/20000)))):cur=nxt
  else:l[i],l[j]=l[j],l[i]
  best=min(best,cur)
 assert best>0
 search.append({'n':n,'trials':20000,'seed':339235+n,'fixed_coloring':colors,'best_score':best,'found':False})
result['bounded_search']=search
# Byte-identical packet and safe extraction, never execute.
p=((B/'expanded-corpus-r246/proof-packet-full.zip') if (B/'expanded-corpus-r246/proof-packet-full.zip').exists() else D/'proof-packet-full.zip').read_bytes(); assert sha(p)=='ffa01d95d108d91cc5f90638a1ef46fd9f76ac2cc743487a2c0b9644e2f7a2ea'
(D/'proof-packet-full.zip').write_bytes(p); dest=D/'packet-safe-extract'; dest.mkdir(exist_ok=True)
with zipfile.ZipFile(D/'proof-packet-full.zip') as z:
 assert set(z.namelist())=={'Mobius.lean','Audit.lean','README.md'}
 for i in z.infolist():
  assert not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size<2000000
  (dest/i.filename).write_bytes(z.read(i))
result['safe_extraction']={'members':{p.name:sha(p.read_bytes()) for p in dest.iterdir()},'packet_sha256':sha(p),'executed':False}
raw=((B/'expanded-corpus-r246/raw/339235.jsonl') if (B/'expanded-corpus-r246/raw/339235.jsonl').exists() else D/'339235.jsonl').read_bytes(); (D/'339235.jsonl').write_bytes(raw); result['raw_sha256']=sha(raw)
assert len(raw.splitlines())==1 and json.loads(raw)
# Preserve directly used evidence, not earlier replay build trees.
for source,rel in [(B/'mobius-review-r1/downloads','sources/review-downloads'),(B/'expanded-corpus-r246/sources','sources/discovery-sources')]:
 if source.exists(): shutil.copytree(source,D/rel,dirs_exist_ok=True)
for src in ['mobius-review-r1/REVIEW.md','mobius-review-r1/logs/math-verification.json','mobius-review-r1/logs/search.log','mobius-root-ruling-r1.json','mobius-parent-final-r1/replay-result.json','mobius-parent-final-r1/registry-refresh.json']:
 target=D/'evidence'/src; target.parent.mkdir(parents=True,exist_ok=True);
 if (B/src).exists(): shutil.copyfile(B/src,target)
result['source_assertions']={'theorem_odd_n':3,'conjectured_even_n':4,'even_threshold':4,'faulty_printed_total':132,'correct_total':2*sum(range(1,13)),'M8_weighted_total':2*15+3*20+3*22,'citing_records':len(json.loads((D/'prior-art-completion.json').read_text())['citing_records'])}
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result['source_assertions'])); print(search)

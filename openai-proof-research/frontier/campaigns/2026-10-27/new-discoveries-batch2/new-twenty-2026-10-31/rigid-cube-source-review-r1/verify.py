from pathlib import Path
import json,itertools,collections,hashlib,time,resource
start=time.time(); resource.setrlimit(resource.RLIMIT_CPU,(30,30)); resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
a=Path('../expanded-corpus-r59'); src=(a/'formal/Cube.lean').read_text(); import re
text=re.search(r'\(\(\[(.*?)\]\.map vertex',src,re.S)
# Extract the list specifically defining A, independent of Python certificate.
nums=re.search(r'def A.*?\(\[(.*?)\]\.map vertex',src,re.S).group(1)
A=[int(x) for x in nums.replace('\n','').split(',')]; vertices=list(itertools.product((-1,1),repeat=8))
def encode(k):return tuple(1 if c=='1' else -1 for c in format(k,'08b')[::-1])
def distance(x,y):return len([None for u,v in zip(x,y) if u!=v])
S=[encode(k) for k in A]; assert len(S)==len(set(S))==34
pairs=[{'x':x,'y':y,'distance':distance(encode(x),encode(y))} for x in A for y in A]
assert max(p['distance'] for p in pairs)==5
rows=[]
for v in vertices:
 ds=[distance(v,w) for w in S]; mx=max(ds); code=sum(2**i for i,c in enumerate(v) if c==1)
 assert mx==5 if v in S else mx>5
 rows.append({'code':code,'coordinates':v,'in_A':v in S,'max_distance':mx,'all_farthest_partners':[A[i] for i,d in enumerate(ds) if d==mx]})
cert=json.loads((a/'certificate.json').read_text()); assert cert['A']==A
for row in cert['rows']:
 own=next(t for t in rows if t['code']==row['x']); assert row['farthest_distance']==own['max_distance'] and row['farthest_witness'] in own['all_farthest_partners']
out={'cardinality':len(S),'ordered_pairs':len(pairs),'distance_histogram':dict(sorted(collections.Counter(p['distance'] for p in pairs).items())),'outside_count':sum(not r['in_A'] for r in rows),'outside_max_distance_histogram':dict(collections.Counter(r['max_distance'] for r in rows if not r['in_A'])),'nonvacuous_pair':next(p for p in pairs if p['distance']==5),'rows':rows,'all_pairs':pairs,'author_certificate_agrees':True,'wall_seconds':time.time()-start,'maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
Path('diagnostics.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps({k:v for k,v in out.items() if k not in ['rows','all_pairs']},indent=2))

import hashlib, json, itertools, collections
from pathlib import Path
from datetime import datetime, timezone

root = Path(__file__).resolve().parent
candidate = root.parent / 'sol-fresh-source-discovery-r114'
def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024*1024), b''): h.update(chunk)
    return h.hexdigest()
entries = [json.loads(line) for line in (candidate/'manifest.jsonl').read_text().splitlines()]
for item in entries:
    p = candidate / item['path']
    assert p.stat().st_size == item['bytes']
    assert sha(p) == item['sha256'], item['path']
freeze = entries + [{'path':'manifest.jsonl','bytes':(candidate/'manifest.jsonl').stat().st_size,'sha256':sha(candidate/'manifest.jsonl')}]
(root/'review-freeze.json').write_text(json.dumps({'candidate':str(candidate),'files':freeze}, indent=2)+'\n')
vertices=[]
for i,j in itertools.combinations_with_replacement(range(10),2):
    x=[0]*10; x[i]+=1; x[j]+=1; vertices.append(tuple(x))
adj={x:[] for x in vertices}
for x in vertices:
    for y in vertices:
        if sum(abs(a-b) for a,b in zip(x,y))==2: adj[x].append(y)
landmark_pairs=[(i,i+1) for i in (0,1,2,3,5,6,7,8)]
landmarks=[]
for i,j in landmark_pairs:
    x=[0]*10;x[i]=x[j]=1;landmarks.append(tuple(x))
distances={}
for x in vertices:
    d={x:0}; q=collections.deque([x])
    while q:
        y=q.popleft()
        for z in adj[y]:
            if z not in d: d[z]=d[y]+1;q.append(z)
    assert len(d)==55
    for y in vertices: assert d[y]==2-sum(min(a,b) for a,b in zip(x,y))
    distances[x]=d
signatures={tuple(distances[x][r] for r in landmarks) for x in vertices}
assert len(signatures)==55
supports=[s for k in range(3) for s in itertools.combinations(range(5),k)]
codes={tuple(int(i in s)+int(i+1 in s) for i in range(4)) for s in supports}
assert len(codes)==16
record={'utc':datetime.now(timezone.utc).isoformat(),'manifest_entries_verified':len(entries),
 'bfs_distances_verified':55*55,'vertices':55,'landmarks':8,'distinct_signatures':len(signatures),
 'block_supports':16,'ordinary_math':'PASS','source_text_scope':'PASS',
 'substantive':'HOLD: close adaptation of Bailey-Cameron Theorem 3.32',
 'novelty':'HOLD','formal':'not started','credit':0,'counts':{'additional':8,'total':38}}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))

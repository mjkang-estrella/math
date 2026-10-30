import json,re,gzip,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
pat=re.compile(r'2407[.-]06132|common.?information|renyi|rényi|dsbs|leiyu|gray.?wyner',re.I)
out=[]
for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json','sol-fresh-source-discovery-r157/sources/omega-delta.json','sol-fresh-source-discovery-r157/sources/openai-delta.json','sol-fresh-source-discovery-r167/registry-screen.json']:
 p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 hits=[x for x in s.splitlines() if pat.search(x)];out.append(dict(path=str(p),sha256=sha(b),hits=hits))
 print(rel, hits)
j=json.loads((L.parent/'sol-fresh-source-discovery-r168/history-qualification.json').read_text())
print('qualification keys',list(j))
(L/'registry-screen.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=out,limits=['Frozen evidence only; no new GitHub requests. Missing merge inventories, capped historical transitions, OpenAI denied current tree and unreviewed bodies remain gaps. No global absence or novelty clearance.']),indent=2)+'\n')

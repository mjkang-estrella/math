import json,gzip,re,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1]
pat=re.compile(r'Paone|line.?graph.{0,70}(?:signature|inertia)|(?:signature|inertia).{0,70}line.?graph|21706797|7192558',re.I)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pattern=pat.pattern,receipts=[],hits=[],omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',comparison_caps=['aa026→a19a capped at300 paths','a19a→490f capped at300 paths'],current_semantic_clearance=False,head_chasing=False)
paths=['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r133/registry-delta-receipt.json','sol-fresh-source-discovery-r137/registry-delta-receipt.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json','sol-fresh-source-discovery-r141/sources/omega-head.json','sol-fresh-source-discovery-r141/sources/openai-head.json','sol-fresh-source-discovery-r144/registry-limits.json']
for rel in paths:
 p=B/'lanes'/rel;b=p.read_bytes();s=(gzip.decompress(b) if p.suffix=='.gz' else b).decode()
 out['receipts'].append(dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),complete_body_read=True))
 for m in pat.finditer(s):out['hits'].append(dict(path=str(p),context=s[max(0,m.start()-250):m.end()+350]))
(L/'registry-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

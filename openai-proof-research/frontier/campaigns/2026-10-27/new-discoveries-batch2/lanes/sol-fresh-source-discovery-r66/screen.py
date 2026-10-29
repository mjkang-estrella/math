import json,pathlib,hashlib,re
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
out={}
for f in [B/'ledger.json',B/'prior-campaign-context.json']:
 d=json.loads(f.read_text()); out[f.name]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'accepted':[(x.get('number'),x.get('title',x.get('id')),x.get('scope')) for x in d.get('accepted',[])]}
for f in [L.parent/'sol-fresh-source-discovery-r57/sources/omega-Problems.json',L.parent/'root-polyomino57-final-review-r1/sources/omega-D5.json',L.parent/'pi-batch2-live-prior-audit-r1/artifacts/d5-tree.json']:
 if not f.exists(): continue
 d=json.loads(f.read_text()); hits=[v['path'] for v in d.get('tree',[]) if re.search('sra|macdonald|turan|monotonic|gamma|henry',v['path'],re.I)]
 out[str(f.relative_to(B))]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'sha':d.get('sha'),'truncated':d.get('truncated'),'hits':hits}
(L/'context-screen.json').write_text(json.dumps(out,indent=2)); print(json.dumps(out,indent=2))

import pathlib,json,hashlib,re
O=pathlib.Path(__file__).resolve().parent;L=O.parent;R=L.parent.parent.parent.parent.parent
p=O/'flat-bindings.json';refs=json.loads(p.read_text())
for path in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',R/'AGENTS.md']:
 if path.is_file():refs.append({'path':str(path),'size':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
p.write_text(json.dumps(refs,indent=2))
versions=[]
for t in sorted((O/'sources').glob('*.txt')):
 m=re.search(r'arXiv:[^\n]+',t.read_text());versions.append({'text':t.name,'version_header':m.group() if m else 'not located; use retained PDF hash'})
(O/'source-versions.json').write_text(json.dumps(versions,indent=2))
p=O/'coverage.json';c=json.loads(p.read_text());c['whole_primary_body_reviews']=0;c['whole_successor_body_readings']=1;c['whole_body_reviews']=1;c['whole_body_limit']='Short 2009.12802 successor read through references; other bodies selected passages only. No upstream dependency replay.';p.write_text(json.dumps(c,indent=2))

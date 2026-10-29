from pathlib import Path
import json,hashlib,re
from html import unescape
P=Path(__file__).resolve().parent
for p in (P/'sources').glob('*.html'):
 (P/'sources'/p.with_suffix('.txt').name).write_text(unescape(re.sub('<[^>]+>', ' ',p.read_text())))
out=[]
for p in P.parent.glob('sol-fresh-source-discovery-r57/sources/*json'):
 try:d=json.loads(p.read_text())
 except:continue
 if 'tree' not in d:continue
 hits=[v['path'] for v in d['tree'] if re.search('arbor|chapoton|preorder|magicposit',v['path'],re.I)]
 out.append(dict(file=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),truncated=d.get('truncated'),hits=hits))
(P/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

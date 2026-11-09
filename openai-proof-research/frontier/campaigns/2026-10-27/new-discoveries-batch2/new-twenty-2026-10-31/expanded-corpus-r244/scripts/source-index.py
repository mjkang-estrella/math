import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text());out[p.parent.name]={'receipt':str(p.relative_to(D)),'status':r.get('status'),'url':r.get('url'),'body_sha256':r.get('sha256')}
 t=p.parent/'text.txt'
 if t.exists():
  lines=t.read_text().splitlines();out[p.parent.name]['text_sha256']=hashlib.sha256(t.read_bytes()).hexdigest();out[p.parent.name]['anchors']=[{'line':n,'text':s} for n,s in enumerate(lines,1) if re.search(r'(Conjecture|Figure|Example|Theorem)',s)]
(D/'source-index.json').write_text(json.dumps(out,indent=2))

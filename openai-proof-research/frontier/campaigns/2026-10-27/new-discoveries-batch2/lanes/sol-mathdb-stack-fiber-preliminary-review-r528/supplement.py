from pathlib import Path
import json,hashlib,urllib.request,datetime,subprocess
D=Path(__file__).resolve().parent;L=D.parent
rows=json.loads((D/'flat-bindings.json').read_text());pairs=[]
def rec(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 root=L/name
 for x in json.loads((root/'bindings.json').read_text()):
  a=Path(x['original']);c=Path(x['copy']);c=c if c.is_absolute() else root/c
  ra,rc=rec(a),rec(c);rows.extend([ra,rc]);pairs.append(dict(original=ra,copy=rc,equal=ra['sha256']==rc['sha256'],copy_matches_recorded=rc['sha256']==x['sha256']))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[3]/'sources/upstream.json',L.parents[3]/'sources/CONTENTS.md',L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md']:
 if p.is_file():rows.append(rec(p))
(D/'flat-bindings.json').write_text(json.dumps(rows,indent=2)+'\n');(D/'history-pair-check.json').write_text(json.dumps(pairs,indent=2)+'\n')
u='https://arxiv.org/pdf/2410.17057v1';r=dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(u,timeout=25) as f:b=f.read();r.update(status=f.status,final_url=f.url)
 p=D/'primary.pdf';p.write_bytes(b);r.update(rec(p));(D/'pdf-binding.json').write_text(json.dumps(r,indent=2)+'\n')
 subprocess.run(['pdftotext','-layout',str(p),str(D/'primary-pdf.txt')],check=True)
 subprocess.run(['pdftoppm','-f','2','-l','3','-scale-to','1300','-png',str(p),str(D/'primary-page')],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
 derived=[rec(p) for p in D.glob('primary-page-*.png')]+[rec(D/'primary-pdf.txt')];(D/'pdf-derivative-bindings.json').write_text(json.dumps(derived,indent=2)+'\n')
except Exception as e:r.update(error=str(e),retry=False);(D/'pdf-binding.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));print('history pairs',len(pairs),'unequal',sum(not x['equal'] for x in pairs))

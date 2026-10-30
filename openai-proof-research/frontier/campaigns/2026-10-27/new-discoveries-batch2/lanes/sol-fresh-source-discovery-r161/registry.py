import json,gzip,re,hashlib,datetime,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent
pat=re.compile(r'Stern|Ulas|10844|343903|Altizio',re.I)
records=[]
for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/registry-delta.json','sol-fresh-source-discovery-r157/sources/omega-delta.json','sol-fresh-source-discovery-r157/sources/openai-delta.json']:
 p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 if p.suffix=='.gz':paths=[x.split('\t')[-1] for x in s.splitlines()]
 else:
  j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))] if isinstance(j,dict) else []
 records.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),hits=[x for x in paths if pat.search(x)],scope='lexical path screen; inherited older two 300-path gaps remain'))
for name,repo,base in [('omega','the-omega-institute/trureturing','b62773edfb6a6f7806de09b593b2e3b6834685c7'),('openai','openai/math','4eaee87548250b2682affda7d05d947c05554bae')]:
 head=json.loads((L/'sources'/f'{name}-head.json').read_bytes())['sha'];r=dict(name=name,base=base,head=head)
 if head!=base:
  url=f'https://api.github.com/repos/{repo}/compare/{base}...{head}';r['url']=url
  try:
   with urllib.request.urlopen(url,timeout=25) as f:b=f.read(12000001);assert len(b)<=12000000
   (L/'sources'/f'{name}-delta.json').write_bytes(b);j=json.loads(b);r.update(files=len(j.get('files',[])),capped=len(j.get('files',[]))>=300,hits=[x['filename'] for x in j.get('files',[]) if pat.search(x['filename'])],sha256=hashlib.sha256(b).hexdigest())
  except Exception as e:r['error']=str(e)
 records.append(r)
(L/'registry-screen.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records,qualification='No worldwide absence or acceptance clearance. Candidate unresolved; target-facing leads require bodies.'),indent=2)+'\n')
for r in records:print(r)

import json,sys,hashlib,re
from pathlib import Path
L=Path(__file__).resolve().parent
if sys.argv[1]=='paths':
 out=[]
 for lane,n in [('sol-fresh-source-discovery-r143','omega-library-tree.json'),('sol-fresh-source-discovery-r143','omega-problems-tree.json'),('sol-fresh-source-discovery-r146','omega-library.json')]:
  p=L.parent/lane/'sources'/n;j=json.loads(p.read_bytes()); hits=[x for x in j['tree'] if re.search(sys.argv[2] if len(sys.argv)>2 else 'mittag|fractional|concavity|li_morgan|siegrist',x['path'],re.I)]
  out.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),truncated=j.get('truncated'),hits=hits))
 (L/('registry-bessel-paths.json' if len(sys.argv)>2 else 'registry-paths.json')).write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
elif sys.argv[1]=='html':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def handle_data(self,d):
   if d.strip():parts.append(d.strip())
 parts=[];P().feed((L/'sources/primary.html').read_text());(L/'sources/primary.txt').write_text('\n'.join(parts))
elif sys.argv[1]=='repair':
 out=[]
 for p in L.glob('history-*.json'):
  j=json.loads(p.read_bytes());tag=p.stem
  for h in j['hits']:
   src=L.parents[5]/h['path'];b=src.read_bytes();assert hashlib.sha256(b).hexdigest()==h['sha256']
   dst=L/'reopened'/tag/str(len(out));dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
   h['copy']=str(dst.relative_to(L));out.append(h['copy'])
  p.write_text(json.dumps(j,indent=2)+'\n')
 print('rebound',len(out),'original-body copies; initial name collision disclosed')
elif sys.argv[1]=='baseline':
 import gzip
 out=[]
 for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/n;h=hashlib.sha256();hits=[]
  with gzip.open(p,'rb') as f:
   for b in f:
    h.update(b)
    if re.search('matuzas|bessel|kloosterman|li.*morgan|inflection',b.decode(),re.I):hits.append(b.decode().strip())
  out.append(dict(path=str(p),uncompressed_sha256=h.hexdigest(),hits=hits))
 (L/'baseline-target-paths.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

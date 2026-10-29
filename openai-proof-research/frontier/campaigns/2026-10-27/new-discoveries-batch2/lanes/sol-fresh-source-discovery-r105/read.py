import pathlib,json,urllib.request,hashlib,re
from html.parser import HTMLParser
L=pathlib.Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
def get(name,url):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=25) as r:b=r.read()
  (L/'sources'/name).write_bytes(b);return b
 except Exception as e:print('FAIL',url,str(e),flush=True);return b''
for name,url in [('heilbronn.raw','https://arxiv.org/html/2603.11107v3'),('classical.raw','https://arxiv.org/html/math/0505020'),('original.pdf','https://strathprints.strath.ac.uk/43070/1/Avgustinovich_etal_DAM2013_avoidance_of_boxed_mesh_patterns_on_permutations.pdf')]:get(name,url)
for p in (L/'sources').glob('*.raw'):
 if p.name.endswith('head.raw'):continue
 h=P();h.feed(p.read_text());s=' '.join(h.a);(p.with_suffix('.txt')).write_text(s)
 if p.stem=='boxed':
  for term in ['7 The remaining','Conjecture 7.4','8 Boxed','J ρ','interleav']:
   start=s.find(term);print(term,start,s[max(0,start-1200):start+9500],flush=True)
 if p.stem=='heilbronn':
  start=s.find('Conjecture 1.');print(s[start-4500:start+2000],flush=True)
omega=json.loads((L/'sources/omega-head.raw').read_bytes());op=json.loads((L/'sources/openai-head.raw').read_bytes());print('HEADS',omega['sha'],op['sha'],flush=True)
base='73a5033dd654a16a14fcd1b13277f1a03d81d826';head=omega['sha']
b=get('omega-delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/{base}...{head}')
if b:
 d=json.loads(b);print('DELTA',d.get('total_commits'),[(f['filename'],f['status']) for f in d.get('files',[])],flush=True)
# current full path inventory, separate from semantic claim clearance
b=get('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}?recursive=1')
if b:
 d=json.loads(b);terms=re.compile('mesh|boxed|Bruhat|Heilbronn|Kitaev|Qiu|Sudermann|2143|degree.*Hasse',re.I);hits=[x['path'] for x in d.get('tree',[]) if terms.search(x['path'])];print('TREE',d.get('truncated'),len(d.get('tree',[])),hits,flush=True)
 for i,path in enumerate(hits):
  if path.endswith(('.lean','.md')):get(f'registry-body-{i}.raw',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{path}')

from pathlib import Path
import json,hashlib,re,subprocess
from html.parser import HTMLParser
b=Path(__file__).parent; root=b.parents[4]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,s):self.parts.append(s)
for name in ['wp']:
 p=Text();p.feed((b/'sources'/f'{name}.html').read_text());(b/'sources'/f'{name}.txt').write_text('\n'.join(p.parts))
for name in ['schubert','gaetz','cai']:
 subprocess.run(['pdftotext','-layout',str(b/'sources'/f'{name}.pdf'),str(b/'sources'/f'{name}.txt')],check=True)
for name in ['omega','openai']:
 j=json.loads((b/'sources'/f'{name}-head.json').read_text());print(name,j['sha'])
p=b.parent/'sol-fresh-source-discovery-r83/sources/omega-compare.json';j=json.loads(p.read_text());print('r83compare', {k:j.get(k) for k in ['status','total_commits','ahead_by','behind_by']},'commits',len(j.get('commits',[])),'files',len(j.get('files',[])),'keys',list(j));print('relevant delta', [f['filename'] for f in j.get('files',[]) if re.search('differential|smith|schubert|miller|reiner',f['filename'],re.I)])
# Complete parsed ledger/prior-context inventory, without relying on truncated terminal reads.
ctx={}
for name in ['ledger.json','prior-campaign-context.json']:
 p=b.parents[1]/name;j=json.loads(p.read_text());ctx[name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'keys':list(j),'entries':{k:[{z:x.get(z) for z in ['number','title','source_target','status','scope','novelty_limit']} for x in v if isinstance(x,dict)] for k,v in j.items() if isinstance(v,list)}}
(b/'context-inventory.json').write_text(json.dumps(ctx,indent=2))

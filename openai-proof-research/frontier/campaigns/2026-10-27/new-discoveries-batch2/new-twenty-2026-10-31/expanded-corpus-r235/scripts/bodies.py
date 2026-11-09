from pathlib import Path
from html.parser import HTMLParser
import re,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fetch import get,D
class T(HTMLParser):
 def __init__(self):super().__init__();self.t=[]
 def handle_data(self,d):self.t.append(d)
for p in sorted((D/'sources').glob('*.abs.html')):
 t=T();t.feed(p.read_text());text=' '.join(' '.join(t.t).split());p.with_suffix('.txt').write_text(text)
 a=p.name.split('.abs')[0]; versions=re.findall(r'\[v(\d+)\]',text); print(a, 'versions', versions, text[text.find('Title:'):text.find('Title:')+110],flush=True)
 for v in versions:get(a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v)

from pathlib import Path
from html.parser import HTMLParser
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i17_six_point_ramsey_novelty_r3'
class Blocks(HTMLParser):
    def __init__(self):super().__init__();self.depth=0;self.active=None;self.blocks=[]
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if tag=='div':
            self.depth+=1
            if 'ltx_theorem' in a.get('class','').split() and self.active is None:self.active={'depth':self.depth,'id':a.get('id'),'text':[]}
        if self.active and tag in ('p','h6'):self.active['text'].append(' ')
    def handle_endtag(self,tag):
        if tag=='div':
            if self.active and self.active['depth']==self.depth:
                self.blocks.append({'id':self.active['id'],'passage':re.sub(r'\s+',' ',''.join(self.active['text'])).strip()});self.active=None
            self.depth-=1
    def handle_data(self,d):
        if self.active:self.active['text'].append(d)
def run():
    out=[]
    for p in sorted((S/'literature').glob('*-html.html')):
        parser=Blocks();parser.feed(p.read_text())
        for b in parser.blocks:
            b.update(file=str(p.relative_to(ROOT)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),passage_sha256=hashlib.sha256(b['passage'].encode()).hexdigest());out.append(b)
    (S/'primary-contracts.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print('Contracts:',len(out))
if __name__=='__main__':run()

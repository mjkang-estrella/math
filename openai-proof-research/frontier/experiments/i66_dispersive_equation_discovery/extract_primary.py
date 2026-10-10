"""Deterministic text extraction. Importing this module never writes."""
from pathlib import Path
from html.parser import HTMLParser
import re, json, subprocess, hashlib

class Extract(HTMLParser):
    def __init__(self):
        super().__init__(); self.parts=[]; self.skip=[]
    def handle_starttag(self, tag, attrs):
        if tag in ['script','style','math']:
            if not self.skip and tag=='math':
                self.parts.append(' '+dict(attrs).get('alttext','')+' ')
            self.skip.append(tag)
        elif tag in ['p','div','section','h1','h2','h3','h4','li','br'] and not self.skip:
            self.parts.append('\n')
    def handle_endtag(self,tag):
        if self.skip and tag==self.skip[-1]: self.skip.pop()
        elif tag in ['p','div','section','h1','h2','h3','h4','li'] and not self.skip:
            self.parts.append('\n')
    def handle_data(self,data):
        if not self.skip: self.parts.append(data)

def extract(data):
    e=Extract(); e.feed(data.decode())
    return '\n'.join(re.sub(r'\s+',' ',s).strip() for s in ''.join(e.parts).splitlines() if s.strip())+'\n'

if __name__=='__main__':
    root=Path(__file__).resolve().parents[3]
    out=root/'frontier/sources/i66_dispersive_equation_discovery/primary'
    records=[]
    for p in sorted(out.glob('*.html')):
        dest=p.with_suffix('.txt'); data=extract(p.read_bytes()).encode(); dest.write_bytes(data)
        records.append({'source':p.name,'text':dest.name,'method':'HTMLParser/MathML alttext','sha256':hashlib.sha256(data).hexdigest()})
    for p in sorted(out.glob('*.pdf')):
        result=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
        dest=p.with_suffix('.txt');dest.write_bytes(result.stdout)
        records.append({'source':p.name,'text':dest.name,'method':'pdftotext -layout','stderr':result.stderr.decode(),'sha256':hashlib.sha256(result.stdout).hexdigest()})
    (out/'extractions.json').write_text(json.dumps(records,indent=2)+'\n')

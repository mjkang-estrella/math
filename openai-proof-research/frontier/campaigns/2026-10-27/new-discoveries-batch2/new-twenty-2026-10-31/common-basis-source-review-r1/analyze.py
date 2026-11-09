from pathlib import Path
import json,re,hashlib,html
L=Path(__file__).resolve().parent;A=L.parent/'expanded-corpus-r250'
r=json.loads((L/'independent-math.json').read_text());c=json.loads((A/'matroid-certificate.json').read_text());assert r['bases']==c['bases']
s=(A/'lean/Bases.lean').read_text().split(':= [',1)[1].split(']',1)[0]; bs=[list(map(int,re.findall(r'\d+',x))) for x in re.findall(r'\{([^}]+)\}',s)]; assert bs==r['bases']
parts=[]
for p in sorted((A/'sources').glob('1601.08199v*.txt')):
 t=p.read_text(); start=t.find('2.'); # retain full relevant section rather than search-hit fragments
 lines=t.splitlines(); hits=[i for i,l in enumerate(lines) if 'Conjecture 13.' in l or 'Conjecture 2.5.' in l]
 parts.append(str(p)+'\n'+ ('\n'.join(lines[max(0,hits[0]-65):hits[0]+90]) if hits else t))
# Strip HTML with standard parser, preserving text boundaries.
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self): super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
for name,p in [('journal',A/'sources/lason-journal.html'),('regular',L/'receipts/regular.html')]:
 parser=Text();parser.feed(p.read_text());(L/(name+'-reading.txt')).write_text('\n'.join(parser.out))
(L/'version-reading.txt').write_text('\n\n'.join(parts))
ledger=L.parent/'ledger.json';d=json.loads(ledger.read_text());(L/'ledger-snapshot.json').write_bytes(ledger.read_bytes());print('LEDGER',d['accepted_new'],d['target_new'])
for tag in ['openai','omega','pool']:
 p=L/'receipts'/(tag+'-head.json')
 if p.exists():
  d=json.loads(p.read_text());print(tag,d['sha'],d['commit']['committer']['date'])
print('ALL 76 AUTHOR CERTIFICATE AND LEAN BASES MATCH INDEPENDENT DETERMINANTS')

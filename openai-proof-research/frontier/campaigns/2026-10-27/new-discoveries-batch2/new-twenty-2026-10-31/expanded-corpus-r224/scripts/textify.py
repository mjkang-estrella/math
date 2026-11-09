from html.parser import HTMLParser
import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
for p in (D/'receipts').glob('*/body'):
 if p.parent.name.endswith(('-html','-abs')):
  t=Text();t.feed(p.read_text(errors='replace'));(D/'sources'/(p.parent.name+'.txt')).write_text('\n'.join(t.out))

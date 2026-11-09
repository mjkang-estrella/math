from pathlib import Path
import runpy
L=Path(__file__).resolve().parent
from html.parser import HTMLParser
class T(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
p=T();p.feed((L/'receipts/larson.html').read_text());(L/'larson-reading.txt').write_text('\n'.join(p.out))

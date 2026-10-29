from pathlib import Path
from html.parser import HTMLParser
import subprocess
P=Path(__file__).resolve().parent
class T(HTMLParser):
 def __init__(self):super().__init__();self.t=[]
 def handle_data(self,d):self.t.append(d)
for n in ['fgr-journal','fgr-html','fgr-abs','madiman']:
 t=T();t.feed((P/'sources'/n).read_text());(P/'sources'/(n+'.txt')).write_text('\n'.join(t.t))
subprocess.run(['pdftotext','-layout',str(P/'sources/fgr-companion'),str(P/'sources/fgr-companion.txt')],check=True)

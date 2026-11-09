from html.parser import HTMLParser
from pathlib import Path
class Text(HTMLParser):
 def handle_data(self,data):
  if data.strip():print(data.strip())
 def handle_starttag(self,tag,attrs):
  if tag=='img':
   for k,v in attrs:
    if k=='alt':print(v)
E=Path(__file__).parent/'evidence'
for n in ['simpson-banach','simpson-szemeredi','simpson-wqo']:
 print('\nSOURCE',n);Text().feed((E/(n+'.txt')).read_text())

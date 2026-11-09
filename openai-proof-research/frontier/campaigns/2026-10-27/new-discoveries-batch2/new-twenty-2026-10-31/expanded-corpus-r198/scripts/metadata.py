import pathlib,json,re
from html import unescape
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*-abs-*/body')):
 s=p.read_text(); i=p.parent.name.split('-')[0]
 print(i, re.findall(r'<meta name="citation_(?:title|author|doi|journal_title)" content="([^"]*)',s));print('DOI',re.findall(r'https://doi.org/[^"<> ]+',s));

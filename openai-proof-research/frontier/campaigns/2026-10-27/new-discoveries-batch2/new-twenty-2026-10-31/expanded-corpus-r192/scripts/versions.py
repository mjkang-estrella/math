import pathlib,re,json,html
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*-abs.body')):
 s=p.read_text();print(p.stem, re.findall(r'<meta name="citation_(?:title|author|doi|pdf_url)" content="(.*?)"',s));i=s.find('Submission history');print(re.sub('<[^>]*>',' ',html.unescape(s[i:i+3200])))

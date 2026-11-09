import pathlib,re,html,json
L=pathlib.Path(__file__).resolve().parent;out=[]
for p in sorted((L/'sources').glob('exact-search*.html')):
 for a in re.findall(r'<li class="arxiv-result">(.*?)</li>',p.read_text(),re.S):
  title=re.search(r'<p class="title[^>]*>(.*?)</p>',a,re.S);ids=re.findall(r'arxiv.org/abs/([^"<>]+)',a)
  t=html.unescape(re.sub('<[^>]+>',' ',title[1] if title else ''))
  out.append({'search':p.name,'id':ids[:1],'title':' '.join(t.split())});print(out[-1])
(L/'exact-results.json').write_text(json.dumps(out,indent=2)+'\n')

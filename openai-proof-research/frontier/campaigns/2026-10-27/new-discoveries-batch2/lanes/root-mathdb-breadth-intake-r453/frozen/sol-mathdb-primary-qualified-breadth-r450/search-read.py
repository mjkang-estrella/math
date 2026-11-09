import pathlib,re,html
L=pathlib.Path(__file__).resolve().parent
for p in sorted((L/'sources').glob('successor-search*.html')):
 s=p.read_text();print(p.name)
 for a in re.findall(r'<li class="arxiv-result">(.*?)</li>',s,re.S):print(html.unescape(re.sub('<[^>]+>',' ',a))[:3500])

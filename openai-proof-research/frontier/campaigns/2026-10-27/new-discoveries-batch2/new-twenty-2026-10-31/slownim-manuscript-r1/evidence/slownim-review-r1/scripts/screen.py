import pathlib,json,re,html
r=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((r/'http').glob('*/receipt.json')):
 d=json.loads(p.read_text());u=d['url'];b=p.parent/'body'
 if d.get('status')!=200: continue
 text=b.read_text(errors='replace')
 if '/search/?searchtype=author' in u:
  print('\nAUTHOR LIST',u)
  blocks=re.split(r'<li class="arxiv-result">',text)[1:]
  for block in blocks:
   title=re.search(r'<p class="title[^>]*>(.*?)</p>',block,re.S)
   if title:
    title=html.unescape(re.sub('<[^>]+>',' ',title[1])).strip();print('TITLE',title)
    if re.search(r'\bnim\b|\bGM-rule\b|screw|remoteness|errat',title,re.I):
     print('RELEVANT',html.unescape(re.sub('<[^>]+>',' ',block)).strip())
 if '/lean-pool/' in u and '/git/trees/' not in u and '/commits/' not in u:
  matches=[(i,line[:400]) for i,line in enumerate(text.splitlines(),1) if re.search(r'\bnim\b|gurvich|naumova|2311.03257|2312.08382|360653|361128|slow.?nim',line,re.I)]
  print('REGISTRY',u,'bytes',len(text),'hits',matches)
 if '/search/repositories?' in u:
  j=json.loads(text);print('GITHUB',u,j['total_count'],[v['full_name'] for v in j.get('items',[])])

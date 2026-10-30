from setup import *
import html,re,sys
def clean(s):return ' '.join(html.unescape(re.sub('<[^>]*>',' ',s)).split())
for n in sys.argv[1:]:
 s=(HERE/'retrieved'/n).read_text();out=[]
 if '<li class="arxiv-result">' in s:
  for x in s.split('<li class="arxiv-result">')[1:]:
   out.append({'url':re.search('https://arxiv.org/abs/[^\"]+',x).group(),'title':clean(re.search(r'<p class="title.*?</p>',x,re.S).group()),'authors':clean(re.search(r'<p class="authors.*?</p>',x,re.S).group()),'abstract':clean(re.search(r'<span class="abstract-full.*?</span>',x,re.S).group())})
 else:
  out=[clean(x) for x in re.findall(r'<li class="b_algo".*?</li>',s,re.S)]
  if not out:out=[clean(s)[:10000]]
 save(n+'.parsed.json',out);print(n,json.dumps(out,indent=2))

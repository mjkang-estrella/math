import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,re,html
L=pathlib.Path(__file__).resolve().parent;out={}
for p in (L/'sources').glob('*abs.html'):
 s=p.read_text();metas=re.findall(r'<meta\s+name="(citation_[^"]+)"\s+content="([^"]*)"',s);versions=re.findall(r'\[v(\d+)\].{0,180}',s)
 text=html.unescape(re.sub('<[^>]+>',' ',s));text=re.sub(r'\s+',' ',text);i=text.find('Submission history')
 d={'meta':metas,'history':text[i:i+1000]};out[p.name]=d
 if any(x in p.name for x in ['331098','330993','328918','matroid','326288']):print(p.name,json.dumps(d))
for n in ['leanpool-head.html','math-head.html']:
 s=(L/'sources'/n).read_text();repo='Vilin97/lean-pool' if n.startswith('lean') else 'openai/math';v=list(dict.fromkeys(re.findall('/'+repo+r'/commit/([0-9a-f]{40})',s)));out[n]={'commit_links_order':v};print(n,v[:3])
for n in ['leanpool-projects.yml','leanpool-index.lean','math-readme.md']:
 s=(L/'sources'/n).read_text();lines=s.splitlines();hits=[{'line':i+1,'text':x} for i,x in enumerate(lines) if re.search(r'Prouhet|Alvir|Cooper|Hypermatrix|ZeroDivisor|Missing.Axiom|330993|331098|328918',x,re.I)];out[n]={'routing_only':True,'hits':hits};print(n,json.dumps(hits)[:3000])
(L/'metadata-review.json').write_text(json.dumps(out,indent=2)+'\n')

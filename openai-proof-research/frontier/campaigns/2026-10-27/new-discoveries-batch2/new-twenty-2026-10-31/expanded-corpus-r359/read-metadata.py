import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,re,html
L=pathlib.Path(__file__).resolve().parent;out={}
for r in json.loads((L/'reservation.json').read_text())['rows']:
 p=L/'sources'/f'{r["mathdb_id"]}.html'
 if not p.exists():continue
 t=p.read_text();m=re.search(r'<blockquote class="abstract[^>]*>(.*?)</blockquote>',t,re.S);a=html.unescape(re.sub('<[^>]+>',' ',m.group(1))) if m else ''
 v=re.findall(r'\[v\d+\].{0,180}',t);j=re.findall(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
 out[str(r['mathdb_id'])]={'abstract':a,'versions_html':v,'journal':j,'version_ids':sorted(set(re.findall(r'/abs/(\d+\.\d+v\d+)',t)))}
 print(r['mathdb_id'],json.dumps(out[str(r['mathdb_id'])]))
(L/'metadata-read.json').write_text(json.dumps(out,indent=2)+'\n')
for name in ['lean-pool-head.html','openai-math-head.html']:
 t=(L/'sources'/name).read_text();print(name,'COMMITS',list(dict.fromkeys(re.findall(r'/commit/([0-9a-f]{40})',t)))[:3])
for name in ['projects.yml','LeanPool.lean']:
 lines=(L/'sources'/name).read_text().splitlines();matches=[(i+1,s) for i,s in enumerate(lines) if re.search('unborder|subdiv|laplacian|Wilmes|quandle|unimodal|Nivat|clique.cover|Galvin|Thue|domination|quasirandom',s,re.I)];print(name,matches[:70])

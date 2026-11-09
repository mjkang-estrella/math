import pathlib,json,re,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
L=pathlib.Path(__file__).resolve().parent;S=L/'sources';C=L.parent
items=[];out={};terms=r'pierc|neural|unimod|downset|lagrang|ramsey|primitive|caputo|elekes|fano|quadratic|tripartite|maximal.dominant'
for label,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 p=S/(label+'-HEAD.html');s=p.read_text();m=re.search(r'"oid":"([0-9a-f]{40})"',s)
 if not m:m=re.search('/'+repo+'/commit/([0-9a-f]{40})',s)
 head=m.group(1) if m else None
 old=C/'common-basis-source-review-r1'/(label+'-paths.json');paths=json.loads(old.read_text());hits=[x for x in paths if x.get('type')=='blob' and re.search(terms,x['path'],re.I)]
 out[label]={'fresh_head':head,'cached_index_path':str(old),'cached_index_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'matching_paths':hits,'limitation':'Cached path index is not assumed complete/current. API host access forbidden after denial; no retry. Bounded names and raw indexes only.'}
 for x in hits:
  path=x['path']
  if (path.endswith('.lean') and label=='pool') or (path.endswith('.tex') and label=='openai') or (label=='omega' and ('Patterns' in path or 'Neural' in path) and path.endswith('.lean')):
   if sum(1 for n,u in items if n.startswith(label+'-match'))<12:items.append([label+'-match-'+str(len(items))+'.txt','https://raw.githubusercontent.com/'+repo+'/'+str(head)+'/'+path])
 for path in (['CONTENTS.md'] if label=='openai' else ['README.md'] if label=='omega' else ['LeanPool.lean','LeanPool/projects.yml']):items.append([label+'-fresh-'+path.replace('/','_'),'https://raw.githubusercontent.com/'+repo+'/'+str(head)+'/'+path])
items += [['ramsey-perondi.pdf','https://mc.sbm.org.br/wp-content/uploads/sites/9/sites/9/2021/12/46-P10.pdf']]
(L/'registry-review.json').write_text(json.dumps(out,indent=2));(L/'registry-fetch.json').write_text(json.dumps(items,indent=2))
for k,v in out.items():print(k,v['fresh_head'],len(v['matching_paths']));print('\n'.join(x['path'] for x in v['matching_paths'][:30]))

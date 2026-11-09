from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;D=L/'http'; jobs=[];out={}
pat=re.compile(r'colorful|outerplanar|bichrom|j170|ding|difference.?set|odd.graph|kneser|induced.forest|clifford|amicab|well.support|pascal|rhombus|narayana|dendrimer|entropy|stress.free|toroidal|abelian.square|blondeau|pauli',re.I)
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 h=json.loads((D/(name+'-head.json')).read_text())['sha'];t=json.loads((D/(name+'-tree.json')).read_text()); matches=[x for x in t.get('tree',[]) if pat.search(x['path'])];out[name]={'head':h,'truncated':t.get('truncated'),'matches':matches}
 print(name,h,'truncated',t.get('truncated'));print('\n'.join(x['path'] for x in matches)[:7000])
 # Fetch full relevant registry roots, plus all textual index candidates.
 for x in t.get('tree',[]):
  p=x['path']
  if x['type']=='tree' and '/' not in p and (p.lower() in ['preprints','leanpool','problems','src','truth','d5']):jobs.append([name+'-subtree-'+p+'.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1'])
  if x['type']=='blob' and (pat.search(p) or (name=='pool' and re.search('index|candidate|projects.yml',p,re.I))) and x.get('size',0)<400000 and re.search(r'\.(md|tex|lean|yml|yaml|json)$',p):jobs.append([name+'-body-'+hashlib.sha256(p.encode()).hexdigest()[:12]+Path(p).suffix,f'https://raw.githubusercontent.com/{repo}/{h}/{p}'])
(L/'registry.json').write_text(json.dumps(out,indent=2));(L/'registry-plan.json').write_text(json.dumps(jobs))
# enumerate each arxiv version and journal reference from complete abs pages
vers={}
for p in D.glob('*-abs.html'):
 s=p.read_text();a=p.name.split('-abs')[0];v=sorted(set(re.findall(a+r'v(\d+)',s)),key=int);vers[a]={'versions':v,'journal':re.findall(r'<td class="tablecell jref">(.*?)</td>',s,re.S),'doi':re.findall(r'https://doi.org/[^"< ]+',s)}
 for n in v:jobs=[]
(L/'versions.json').write_text(json.dumps(vers,indent=2));print('versions',json.dumps(vers))

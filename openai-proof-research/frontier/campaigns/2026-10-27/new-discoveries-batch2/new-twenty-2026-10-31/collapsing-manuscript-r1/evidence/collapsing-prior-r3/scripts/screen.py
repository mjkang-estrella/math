from fetch import *
import re
out=[]
pat=re.compile(r'Eriksson|Fienberg|Rinaldo|Sullivant|378395|Dressian|tropical.{0,20}hyperplane|marginal.{0,20}cone|log.linear|no.three.way',re.I)
for n in ['D5','Problems']:
 t=json.loads((BASE/'sources'/('omega-'+n+'-tree.json')).read_text());assert t['truncated']==False
 for i,e in enumerate(json.loads((BASE/'outputs'/('omega-'+n+'-hits.json')).read_text())):
  if e['type']!='blob':continue
  p=BASE/'sources/omega-hits'/(n+'-'+str(i)+'.txt');s=p.read_text();assert len(p.read_bytes())==e['size'];assert hashlib.sha1(b'blob '+str(e['size']).encode()+b'\0'+p.read_bytes()).hexdigest()==e['sha']
  doc=re.search(r'/[-*!]+(.*?)(?:-/)',s,re.S)
  desc=(doc.group(1) if doc else s)[:500]
  matches=[{'line':j+1,'text':l} for j,l in enumerate(s.splitlines()) if pat.search(l)]
  out.append({'tree':n,'path':e['path'],'blob_sha1_verified':True,'body_bytes':len(p.read_bytes()),'description_excerpt':desc,'specific_hits':matches})
(BASE/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for x in out:print(x['tree'],x['path'],'\n',x['description_excerpt'][:210].replace('\n',' '),'\n specific:',x['specific_hits'])

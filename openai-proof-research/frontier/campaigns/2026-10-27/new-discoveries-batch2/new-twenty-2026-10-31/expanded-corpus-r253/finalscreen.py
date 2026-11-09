from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;D=L/'http';pat=re.compile(r'colorful|outerplanar|bichrom|J170|Difference.?Sets|Odd.?Graph|Kneser|Induced.?Forest|Clifford|Amicab|Well.?Supported|Pascal.?Rhombus|Narayana|Dendrimer|Eccentricity.?Entropy|Graph.?Entropy|Stress.?Free|Toroidal|Abelian.?Square|Blondeau|Pauli',re.I)
out={}; jobs=[]
for p in [D/'openai-preprints-full.json',D/'omega-specific-D5_S1_Words.json']:
 t=json.loads(p.read_text());m=[x for x in t.get('tree',[]) if pat.search(x['path'])];out[p.name]={'truncated':t.get('truncated'),'entries':len(t.get('tree',[])),'matches':m};print(p.name,'truncated',t.get('truncated'));print('\n'.join(x['path'] for x in m))
 for x in m:
  if p.name.startswith('openai') and x['type']=='blob' and x['path'].endswith('.tex'):jobs.append(['oai-preprint-'+hashlib.sha256(x['path'].encode()).hexdigest()[:12]+'.tex','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/'+x['path']])
for p in list(D.glob('pool-index*'))+[D/'projects.yml']:
 if 'receipt' in p.name:continue
 lines=[{'line':n,'text':s} for n,s in enumerate(p.read_text().splitlines(),1) if pat.search(s)];out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matches':lines};print(p.name,str(lines)[:1000])
(L/'registry-final.json').write_text(json.dumps(out,indent=2));(L/'matched-plan.json').write_text(json.dumps(jobs))

from pathlib import Path
import json,re,hashlib,subprocess,resource
P=Path(__file__).resolve().parent;R=P.parent/'expanded-corpus-r254'
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
items=[]
for name,src in [('abm-v1',P/'abm-v1.txt'),('abm-v2',P/'abm-v2.txt'),('abm-v3',P/'abm-v3.txt'),('secondary-v1',R/'1510.00777v1-pdf.txt'),('secondary-v2',P/'secondary-v2.txt'),('successor',R/'elvey-pdf.txt')]:
 s=src.read_text();pages=s.split('\f');entries=[]
 for i,page in enumerate(pages,1):
  lines=page.splitlines()
  for j,l in enumerate(lines):
   if re.search(r'Figure\s+[AB.\d]+:|Table\s+\d|Example|\(P[12] |\(N[123] |Conjecture 4\.',l):entries.append({'pdf_page':i,'text':'\n'.join(lines[max(0,j-1):j+4])})
 items.append({'name':name,'file':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'pages':len(pages)-1,'inventory':entries})
(P/'body-inventory.json').write_text(json.dumps(items,indent=2))
# Exact source pages, no witness calculation.
for n,a,b in [('abm-v3',32,33),('secondary-v2',14,16)]:
 subprocess.run(['pdftoppm','-f',str(a),'-l',str(b),'-scale-to','1500','-png',str(P/(n+'.body')),str(P/(n+'-page'))],check=True,timeout=20)
# Preserve relevant text passages without altering source inputs.
passages=[]
for name,src,terms in [('abm-v3',P/'abm-v3.txt',['Conjecture 10.','Proposition 19.','Proposition 20.','6.3.1.','(N1','(N2','(N3']),('secondary-v1',R/'1510.00777v1-pdf.txt',['Conjecture 4.1','Theorem 3.13.']),('secondary-v2',P/'secondary-v2.txt',['Theorem 2.16.','Theorem 3.13.','Conjecture 4.1','Conjecture 4.2']),('successor',R/'elvey-pdf.txt',['Theorem 2.11.','We were not able'])]:
 s=src.read_text()
 for t in terms:
  a=s.find(t);passages.append('\nSOURCE '+name+' TERM '+t+'\n'+(s[max(0,a-100):a+4500] if a>=0 else 'NOT FOUND'))
(P/'source-passages.txt').write_text('\n'.join(passages))
# Read all ledgers, preserve exact-topic entries only; avoid treating arbitrary number collisions as matches.
context=[]
for f in [P.parent/'ledger.json',P.parent.parent/'ledger.json',P.parent.parent/'prior-campaign-context.json']:
 d=json.loads(f.read_text());hits=[]
 def walk(v):
  if isinstance(v,dict):
   ss=json.dumps(v)
   if any(str(v.get(k)) in ['331498','347913'] for k in ['mathdb_id','related_mathdb_id']):hits.append(v);return
   if len(ss)<18000 and re.search('Marshall|path shuffle|Bousquet|peak.count|balanced path|polynomial positivity',ss,re.I):hits.append(v);return
   for x in v.values():walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 walk(d);context.append({'file':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'count':d.get('accepted_new'),'target':d.get('target_new'),'matches':hits})
(P/'local-history.json').write_text(json.dumps(context,indent=2))
print('inventory and passages written')

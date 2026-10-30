from pathlib import Path
import json,re,datetime,hashlib,urllib.request,urllib.parse,urllib.error,xml.etree.ElementTree as ET
h=Path(__file__).resolve().parent;c=h/'copies/sol-fresh-source-discovery-r189'
aliases=['2003.12653','1412.5734','integer-valued polynomials','Guo','Schmidt','divisibility','double factorial','merge-tree','capped']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'administrative':{},'history':{},'versions':{},'live_registry':{}}
for name in ['ledger.json','prior-campaign-context.json']:
 data=json.loads((h/'administrative'/name).read_text()); hits=[]
 def walk(x,path=''):
  if isinstance(x,dict):
   for k,v in x.items():walk(v,path+'/'+k)
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,path+'/'+str(i))
  elif isinstance(x,str) and any(a.lower() in x.lower() for a in aliases):hits.append({'path':path,'text':x})
 walk(data);out['administrative'][name]={'top_keys':list(data),'relevant_records':hits,'read_all_json':True}
for name in ['history-r185.json','history-r186.json','history-r187.json','history-receipt.json','early-screen.json','registry-screen.json','exact-alias-screen.json','search.jsonl']:
 text=(c/name).read_text();lines=text.splitlines()
 hits=[{'line':i+1,'text':s[:1000]} for i,s in enumerate(lines) if any(a.lower() in s.lower() for a in aliases[:7])]
 out['history'][name]={'bytes':len(text.encode()),'matches':hits[:60],'matches_total':len(hits),'limitation':'Recorded index/screen evidence only; not rereading all 2550 historical primary documents'}
for name in ['guo-abs.html','chen-abs.html']:
 text=(h/'live'/name).read_text()
 pos=text.find('Submission history');out['versions'][name]=re.sub('<[^>]+>',' ',text[pos:pos+2200])
text=(h/'live/registry.json').read_text()
for a in aliases[:7]:
 hits=list(re.finditer(re.escape(a),text,re.I))
 out['live_registry'][a]={'count':len(hits),'contexts':[text[max(0,m.start()-160):m.end()+220] for m in hits[:12]]}
queries=['"2003.12653" proof','"Guo" "conjecture" "double factorial"']
out['searches']=[]
for i,q in enumerate(queries):
 url='https://www.bing.com/search?format=rss&q='+urllib.parse.quote(q)
 row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'query':q,'url':url}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:body=r.read(1_000_001);row.update(status=r.status,final_url=r.url)
  assert len(body)<=1_000_000
  (h/'live'/f'search-{i}.xml').write_bytes(body);row['sha256']=hashlib.sha256(body).hexdigest()
  row['items']=[{n:x.findtext(n) for n in ['title','link','description']} for x in ET.fromstring(body).findall('.//item')]
 except Exception as e:
  row['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):
   body=e.read();(h/'live'/f'search-{i}.error').write_bytes(body);row['error_body_sha256']=hashlib.sha256(body).hexdigest()
 out['searches'].append(row)
(h/'comparison-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'versions':out['versions'],'registry':out['live_registry'],'searches':out['searches']},indent=2))

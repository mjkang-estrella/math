import pathlib,json,urllib.request,urllib.parse,hashlib,datetime,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).parent;ns={'a':'http://www.w3.org/2005/Atom'};out=[]
queries=['all:"two abnormal edges"','all:"normal edge coloring" AND all:"Putman"','all:"sublinear approximations"']
entries=json.loads((L/'scout'/'entries.json').read_text());selected=[e for e in entries if not e['id'].startswith(('2105.00382','2105.00551'))]
queries+=['ti:'+e['title'].replace('[','').replace(']','') for e in selected]
for i,q in enumerate(queries):
 u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':4,'sortBy':'lastUpdatedDate','sortOrder':'descending'});r={'query':q,'url':u,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(u,timeout=12) as f:b=f.read(250001);assert len(b)<=250000;r['status']=f.status
  p=L/'current'/('prior-'+str(i)+'.xml');p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest())
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  root=ET.fromstring(b);r['entries']=[{'id':e.findtext('a:id',namespaces=ns),'title':e.findtext('a:title',namespaces=ns),'updated':e.findtext('a:updated',namespaces=ns)} for e in root.findall('a:entry',ns)]
 except Exception as e:r['failure']=repr(e)
 out.append(r)
(L/'prior-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
admin={}
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text());admin[name]={'accepted':[{'number':a.get('number'),'title':a.get('title'),'scope':a.get('scope')} for a in d['accepted']]}
(L/'administrative-read.json').write_text(json.dumps(admin,indent=2))
hits=[];count=0;ids=[e['id'].split('v')[0] for e in selected]
for lane in sorted(L.parent.iterdir()):
 if not lane.is_dir() or lane==L:continue
 for name in ['SUMMARY.md','SCOUTING.md','discovery.md']:
  p=lane/name
  if not p.is_file() or p.stat().st_size>150000:continue
  count+=1;s=p.read_text(errors='replace');found=[i for i in ids if i in s]
  if found:hits.append({'path':str(p),'ids':found,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'history-alias-screen.json').write_text(json.dumps({'files_scanned':count,'exact_identifier_only':True,'hits':hits},indent=2));print('history',count,hits)

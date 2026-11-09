import pathlib,urllib.request,urllib.parse,json,hashlib,xml.etree.ElementTree as E,datetime
L=pathlib.Path(__file__).parent;out=[];ns={'a':'http://www.w3.org/2005/Atom'}
terms=['ti:"Petersen" AND (all:"abnormal" OR all:"counterexample")','ti:"linear derivations" AND au:Tian','ti:"Skolem" AND au:Hajdu','ti:"overlapping families"','ti:"semi-regular continuants"','ti:"UMEBs" AND au:Levick','ti:"growable realizations"','ti:"finite quotients" AND au:Liu','ti:"Brauer-Siegel" AND au:Griffon']
for i,q in enumerate(terms):
 u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':8,'sortBy':'lastUpdatedDate','sortOrder':'descending'});r={'query':q,'url':u,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(u,timeout=12) as f:b=f.read(200001);assert len(b)<=200000;r['status']=f.status
  p=L/'current'/('precise-'+str(i)+'.xml');p.write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  r['entries']=[{'id':e.findtext('a:id',namespaces=ns),'title':e.findtext('a:title',namespaces=ns),'published':e.findtext('a:published',namespaces=ns),'updated':e.findtext('a:updated',namespaces=ns)} for e in E.fromstring(b).findall('a:entry',ns)]
 except Exception as e:r['failure']=repr(e)
 out.append(r)
(L/'prior-precise.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

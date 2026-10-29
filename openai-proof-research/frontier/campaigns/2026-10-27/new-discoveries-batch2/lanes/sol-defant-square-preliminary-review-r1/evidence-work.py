import resource,signal,hashlib,json,urllib.request,datetime,re,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
b=Path(__file__).resolve().parent; lanes=b.parent
coverage=json.loads((lanes/'sol-fresh-analysis-source-r22/coverage.json').read_text()); log=json.loads((lanes/'sol-fresh-analysis-source-r22/http-log.json').read_text())
records=[]
files=[('omega-D5',lanes/'sol-fresh-analysis-source-r22/sources/omega-D5-current-tree.json'),('omega-Problems',lanes/'sol-fresh-analysis-source-r22/sources/omega-Problems-current-tree.json'),('aim',lanes/'root-log-arctangent-acceptance-r1/aim-screen/tree.json'),('openai',lanes/'sol-mean-cascade-current-prior-audit-r1/sources/openai-preprints-tree.json'),('count',lanes/'sol-mean-cascade-current-prior-audit-r1/sources/count-full-tree.json')]
expected={'aim':'4bc0a5435be43e35c261b621009035c92b3ee36e7881685dea41bd742f888537','openai':'6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305','count':'dd68492cd9f027d3f58475fc805b091d3f312bec64039b624349024ea952dc41'}
for label,f in files:
 data=f.read_bytes();h=hashlib.sha256(data).hexdigest();j=json.loads(data)
 match=[v for v in log if v.get('name')==f.name and v.get('sha256')==h]
 if label.startswith('omega'):
  receipt=json.loads((lanes/'sol-fresh-analysis-source-r22/provenance.json').read_text())['artifacts']['sources/'+f.name]
  assert h==receipt['sha256'];match=[receipt]
 else:assert h==expected[label]
 assert j.get('truncated') is False
 hits=[v for v in j['tree'] if re.search('schemmel|defant|1412.?3080|329432|329433|sparse.*totient|totient.*sparse',v['path'],re.I)]
 broad=[v['path'] for v in j['tree'] if re.search('totient|prime.?square',v['path'],re.I)]
 records.append(dict(label=label,file=str(f),sha256=h,sha=j['sha'],entries=len(j['tree']),truncated=False,original_retrieval=match,hits=hits,broad_hits=broad))
(b/'evidence/registry-screen.json').write_text(json.dumps(dict(records=records,coverage=coverage,limit='09:05 saved complete snapshots, no new heads or GitHub requests, path screens are not semantic clearance'),indent=2))
print(json.dumps([dict(label=r['label'],sha256=r['sha256'],entries=r['entries'],hits=r['hits']) for r in records],indent=2))
http=[]
for name,url in [('author.html','https://sites.google.com/view/colin-defant/research'),('citer-graph.pdf','https://archive.intlpress.com/site/pub/files/_fulltext/journals/joc/2020/0011/0002/JOC-2020-0011-0002-a006.pdf'),('clopen-current.html','https://clopen.solutions/')]:
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical review (public read-only)'}),timeout=12) as res:
   d=res.read(8*1024**2+1);assert len(d)<=8*1024**2
   row.update(status=res.status,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));(b/'evidence'/name).write_bytes(d)
 except Exception as e:row['error']=str(e)
 http.append(row)
(b/'evidence/http.json').write_text(json.dumps(http,indent=2));print(json.dumps(http,indent=2))
if (b/'evidence/citer-graph.pdf').exists():subprocess.run(['pdftotext','-layout',str(b/'evidence/citer-graph.pdf'),str(b/'evidence/citer-graph.txt')],check=True,timeout=10)

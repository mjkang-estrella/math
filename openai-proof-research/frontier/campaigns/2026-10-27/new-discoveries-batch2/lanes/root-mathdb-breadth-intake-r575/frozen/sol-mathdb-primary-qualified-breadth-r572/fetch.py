import pathlib,json,hashlib,urllib.request,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent
bs=json.loads((P/'flat-bindings.json').read_text())
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 p=L/rel;b=p.read_bytes();bs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'flat-bindings.json').write_text(json.dumps(bs,indent=2)+'\n')
log=[]
for aid in ['2602.17459','2605.07380','2605.26916','math/0205071','math/0508362','math/0610410','math/0606072']:
 url='https://arxiv.org/html/'+aid
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source screening'}),timeout=25) as r:b=r.read();final=r.url
  name=aid.replace('/','_')+'.html';(P/name).write_bytes(b)
  log.append({'requested_url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'status':200})
 except Exception as e:log.append({'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':str(e),'retry':False})
 (P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))

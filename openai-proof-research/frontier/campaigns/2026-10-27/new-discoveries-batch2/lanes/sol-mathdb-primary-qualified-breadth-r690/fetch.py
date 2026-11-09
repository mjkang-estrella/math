import pathlib,json,hashlib,urllib.request,urllib.error,datetime
P=pathlib.Path(__file__).resolve().parent;events=[]
for id,url in [('335423','https://arxiv.org/html/1703.00003v1'),('406505','https://arxiv.org/html/2610.20097v1')]:
 ev={'mathdb_id':int(id),'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Python-urllib/3'},'coverage':'unread bytes'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=ev['headers']),timeout=25) as r:
   b=r.read(12000000);ev.update({'status':r.status,'final_url':r.url,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'path':id+'.html'});(P/(id+'.html')).write_bytes(b)
 except Exception as e:ev.update({'failure':str(e),'retry':False})
 events.append(ev)
(P/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n');print(json.dumps(events))

from pathlib import Path
import json,hashlib,urllib.request,urllib.error,subprocess,datetime
O=Path(__file__).parent;L=O.parent;S=O/'sources';S.mkdir(exist_ok=True)
refs=json.loads((O/'flat-bindings.json').read_text());events=[]
def bind(p):
 b=p.read_bytes();refs.append({'path':str(p.resolve()),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
cache={'2008.01012':L/'astra-algebra-matrix-r2/sources/2008.01012.pdf','2006.15287':L/'sol-mathdb-primary-qualified-breadth-r476/sources/2006.15287v5.pdf'}
for a in ['2008.01012','2006.15287','2005.07357','2008.13475','2008.00926','2006.03414','2009.06331','2011.02450','2010.00580','2008.05165','2007.01808','2007.07042','2009.01086','2010.08172']:
 url='https://arxiv.org/pdf/'+a;p=S/(a+'.pdf');event={'arxiv':a,'url':url,'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if a in cache:
   bind(cache[a]);p.write_bytes(cache[a].read_bytes());event['cached_original']=str(cache[a])
  else:
   with urllib.request.urlopen(url,timeout=12) as r:
    b=r.read();event.update(status=r.status,final_url=r.url,headers=dict(r.headers));assert b.startswith(b'%PDF');p.write_bytes(b)
  bind(p);t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);bind(t);event['result']='PDF and derivative bound before reading'
 except Exception as e:
  event['failure']=repr(e);events.append(event)
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):
   event['route_stop']='No more arxiv requests in this run';break
  continue
 events.append(event)
 (O/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n')
(O/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n');print(json.dumps(events,indent=2))

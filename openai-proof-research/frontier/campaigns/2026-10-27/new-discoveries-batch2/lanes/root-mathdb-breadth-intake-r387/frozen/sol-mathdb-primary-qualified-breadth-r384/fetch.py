from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True)
rows=json.loads((R/'records.json').read_text()); wanted={343658,347329,347713,353513,354056,354775,359300,360101,362899,367623,369478,370515,373517,375050,381305,381830}
requests=[(str(x['mathdb_id']),'https://arxiv.org/pdf/'+x['source_url'].split('/abs/')[1]) for x in rows if x['mathdb_id'] in wanted]
requests += [('381305-successor','https://www.ejgta.org/index.php/ejgta/article/download/1414/pdf_247')]
log=[];blocked=set()
for key,url in requests:
 host=urllib.parse.urlsplit(url).netloc
 if host in blocked: log.append({'key':key,'url':url,'status':'not_attempted_host_hold'});continue
 e={'key':key,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification (public scholarly PDF)'}),timeout=12) as f: data=f.read(12000000);e['final_url']=f.url;e['http_status']=f.status
  assert data.startswith(b'%PDF'), 'not PDF / possible challenge'
  p=R/'sources'/f'{key}.pdf';p.write_bytes(data);e.update(status='retained',sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
 except Exception as ex:
  e.update(status='failure',error=str(ex))
  if isinstance(ex,urllib.error.HTTPError) and ex.code in (403,429):blocked.add(host)
 log.append(e);print(key,e['status'],flush=True)
 (R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')

from pathlib import Path
import json,urllib.request,urllib.error,hashlib,datetime,subprocess
L=Path(__file__).parent;(L/'sources').mkdir(exist_ok=True)
xs=json.loads((L/'assigned-records.json').read_text());out=[];blocked=False
for url in dict.fromkeys(v['record']['source_url'] for v in xs):
 aid=url.rsplit('/',1)[-1]; target='https://arxiv.org/pdf/'+aid; row={'source_url':url,'request_url':target,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'arXiv current redirect/body; inspect version in extracted header','whole_body_audit':False}
 if blocked:row['status']='HOLD: earlier access-control stop';out.append(row);continue
 try:
  with urllib.request.urlopen(target,timeout=12) as r:
   data=r.read(12000000);row.update(final_url=r.url,http_status=r.status)
  assert data.startswith(b'%PDF') and len(data)<12000000
  p=L/'sources'/f'{aid}.pdf';p.write_bytes(data);row.update(status='retained_not_yet_read',path=str(p.resolve()),size=len(data),sha256=hashlib.sha256(data).hexdigest())
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=12)
  row['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:
  row.update(status='HOLD: source access/extraction failure',error=repr(e))
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:blocked=True
 out.append(row);print(aid,row['status'],flush=True)
 (L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')

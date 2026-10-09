#!/usr/bin/env python3
import concurrent.futures,hashlib,json,pathlib,subprocess,urllib.request
HERE=pathlib.Path(__file__).resolve().parent
entries=[('pintz-v1','https://arxiv.org/pdf/1004.1067v1'),('shao','https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf'),('lichtman-v2','https://arxiv.org/pdf/2009.08969v2'),('ford-sigphi','https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf'),('carella-v1','https://arxiv.org/pdf/2206.12956v1')]
def fetch(pair):
 name,url=pair
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read()
  assert b.startswith(b'%PDF')
  p=HERE/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(HERE/(name+'.txt'))],check=True)
  return {'url':url,'local':p.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches_author':b==(HERE.parent/'i05_parity_pd'/p.name).read_bytes()}
 except Exception as e:return {'url':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:out=list(ex.map(fetch,entries))
(HERE/'literature-manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

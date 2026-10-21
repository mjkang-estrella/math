from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r133/private/primary')
items=[('wu-yau-published','https://archive.ymsc.tsinghua.edu.cn/pacm_download/21/11836-WuYau_JAMS_published.pdf'),('hedenmalm-1989','https://people.kth.se/~haakanh/publications/hed-blms.pdf'),('shcherbina-zhang-v1','https://arxiv.org/pdf/2003.06728v1'),('hwang-singer-v1','https://arxiv.org/pdf/math/9811024v1'),('hao-chen-wang-v1','https://arxiv.org/pdf/2509.04179v1'),('hao-chen-wang-zhang-v1','https://arxiv.org/pdf/2609.14482v1')]
def get(item):
 name,url=item
 try:
  b=urllib.request.urlopen(url,timeout=40).read()
  if not b.startswith(b'%PDF'): raise ValueError('not PDF')
  p=R/(name+'.pdf');p.write_bytes(b)
  t=R/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,capture_output=True)
  return {'name':name,'url':url,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'pages':len(t.read_text().split('\f'))-1}
 except Exception as e:return {'name':name,'url':url,'failure':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex: records=list(ex.map(get,items))
(R/'acquisition.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))

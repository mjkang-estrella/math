exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
from concurrent.futures import ThreadPoolExecutor
R=json.loads((L/'reservation.json').read_text())
jobs=[(u.split('/')[-1]+'.abs.html',u) for u in dict.fromkeys(x['source_url'] for x in R['rows'])]
jobs += [('1708.04841.pdf','https://arxiv.org/pdf/1708.04841'),('spectral-journal.pdf','https://ems.press/content/serial-article-files/36601'),('openai-current.html','https://github.com/openai/math'),('openai-current-CONTENTS.md','https://raw.githubusercontent.com/openai/math/main/CONTENTS.md'),('leanpool-current.html','https://github.com/Vilin97/lean-pool'),('leanpool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml'),('leanpool-index.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool.lean')]
def run(job):
 name,url=job;t=time.monotonic();info={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ordinary-source-review/1.0'}),timeout=10) as q:
   b=q.read(16000001);assert len(b)<=16000000;info.update(status=q.status,final_url=q.url,bytes=len(b),sha256=sha(b),content_type=q.headers.get('Content-Type'));put('sources/'+name,b)
 except Exception as e:info.update(status=getattr(e,'code',None),error=repr(e))
 info['duration_s']=time.monotonic()-t;js('http/'+name+'.json',info);return info
with ThreadPoolExecutor(max_workers=2) as pool: rows=list(pool.map(run,jobs))
js('acquisition-batch.json',rows);print(json.dumps(rows,indent=2));receipt('batch',{'true_exit':0,'threads':2,'joined':True})

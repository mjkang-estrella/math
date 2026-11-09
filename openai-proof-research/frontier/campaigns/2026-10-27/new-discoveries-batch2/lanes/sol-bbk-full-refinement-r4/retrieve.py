#!/usr/bin/env python3
from pathlib import Path
import urllib.request, urllib.error, json, datetime, hashlib
from concurrent.futures import ThreadPoolExecutor
B=Path(__file__).resolve().parent; S=B/'sources';S.mkdir(exist_ok=True); records=[]
def get(name,url):
 r=dict(file='sources/'+name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research (public read only)'}),timeout=35) as f:
   d=f.read(24000000);r['status']=f.status
  (S/name).write_bytes(d);r.update(bytes=len(d),sha256=hashlib.sha256(d).hexdigest())
  return json.loads(d) if name.endswith('.json') else d
 except Exception as e:r['error']=str(e);return None
 finally: records.append(r)
def save(): (B/'retrieval.json').write_text(json.dumps(records,indent=2))
if __name__=='__main__':
 try:
  jobs=[('bbk.html','https://arxiv.org/html/2601.04014v1'),('lecture.html','https://arxiv.org/html/math/0309108v1'),('gk.pdf','https://arxiv.org/pdf/2502.06032v3'),('bbk-abs.html','https://arxiv.org/abs/2601.04014'),('mathdb.html','https://mathdb.math.ru.nl/conjectures/372432')]
  with ThreadPoolExecutor(max_workers=3) as ex:list(ex.map(lambda z:get(*z),jobs))
  for label,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
   h=get(label+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
   if not h:continue
   root=get(label+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h["sha"]}')
   if not root:continue
   for e in root.get('tree',[]):
    if e['type']=='tree':
     tree=get(label+'-'+e['path']+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{e["sha"]}?recursive=1')
     if tree:
      hits=[x for x in tree.get('tree',[]) if any(t in x['path'].lower() for t in ['04014','372432','bachraoui','banerjee','bbk'])]
      print(label,e['path'],'truncated',tree.get('truncated'),'entries',len(tree.get('tree',[])),'hits',hits)
      for j,x in enumerate(hits):
       if x['type']=='blob':get(label+'-'+e['path']+'-hit'+str(j)+'.txt',f'https://raw.githubusercontent.com/{repo}/{h["sha"]}/{e["path"]}/{x["path"]}')
 finally:save();print(json.dumps(records,indent=2))

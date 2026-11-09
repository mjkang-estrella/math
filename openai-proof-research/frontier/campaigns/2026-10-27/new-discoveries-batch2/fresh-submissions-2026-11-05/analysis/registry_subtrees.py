from pathlib import Path
import requests,json,hashlib,concurrent.futures,subprocess
p=Path(__file__).parent;jobs={
'openai-preprints':'https://api.github.com/repos/openai/math/git/trees/3f56f68a176b4494c346091ea0a319651bc217ec?recursive=1',
'trureturing-Library':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/56f21a9b771b3ea7ffd5056c03b486ce31897ab2?recursive=1',
'geng-shen-song':'https://arxiv.org/pdf/1608.07736v1',
'cummings-feng':'https://www.worldscientific.com/doi/pdf/10.1142/S021820250600108X'}
def go(k,u):
 try:
  r=requests.get(u,timeout=35);b=r.content;ext='pdf' if b.startswith(b'%PDF') else 'json' if 'api.github' in u else 'html';f=p/'sources'/(k+'.'+ext);f.write_bytes(b);rec=dict(url=u,status=r.status_code,sha256=hashlib.sha256(b).hexdigest(),path=str(f))
  if ext=='json':
   d=r.json();rec.update(truncated=d.get('truncated'),entries=len(d.get('tree',[])),hits=[x['path'] for x in d.get('tree',[]) if any(w in x['path'].lower() for w in ['korn','cummings','lorton','komornik','319645','329722'])])
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],capture_output=True,timeout=10)
  return rec
 except Exception as e:return dict(url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e:r=list(e.map(lambda z:go(*z),jobs.items()))
(p/'subtree-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))

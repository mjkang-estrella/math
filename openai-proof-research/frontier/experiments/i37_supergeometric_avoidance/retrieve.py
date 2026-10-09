from pathlib import Path
import json,hashlib,urllib.request,datetime,concurrent.futures,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i37_supergeometric_avoidance/literature'; S.mkdir(parents=True,exist_ok=True)
prior=json.loads((R/'frontier/sources/i36_common_geometric_avoidance_novelty_r3/literature/manifest.json').read_text())
requests=[x for x in prior if x['name'] not in ['survey-current','withdrawn-current','burgin-v1','burgin-current']]
requests += [dict(name='burgin-current',url='https://arxiv.org/abs/2210.09284'),dict(name='twofold-current',url='https://arxiv.org/abs/2607.03584'),dict(name='twofold-v2',url='https://arxiv.org/pdf/2607.03584v2')]
def get(row):
 name,url=row['name'],row['url'];rec=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 research-source-verification'}),timeout=45) as f:
   b=f.read();rec.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  suffix='.pdf' if b.startswith(b'%PDF') else '.html';p=S/(name+suffix);p.write_bytes(b)
  rec.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if 'path' in row:rec['same_as_prior']=b==(R/row['path']).read_bytes()
  if suffix=='.pdf':
   run=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True); rec.update(extraction_exit=run.returncode,extraction_stderr=run.stderr)
 except Exception as e:rec['error']=repr(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex: rows=list(ex.map(get,requests))
(S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k in ['name','status','bytes','error','same_as_prior']} for x in rows],indent=2))

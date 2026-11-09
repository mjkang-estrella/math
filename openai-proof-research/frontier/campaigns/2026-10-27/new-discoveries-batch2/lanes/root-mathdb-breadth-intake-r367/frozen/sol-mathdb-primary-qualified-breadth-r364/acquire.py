from pathlib import Path
import json,urllib.request,hashlib,datetime,subprocess
R=Path(__file__).parent
sources=[('337039','https://arxiv.org/pdf/1709.03449'),('320288','https://arxiv.org/pdf/1008.2583'),('341533','https://arxiv.org/pdf/1901.02468'),('340760','https://arxiv.org/pdf/1810.06984'),('325538','https://arxiv.org/pdf/1305.1867')]
rows=[]
for id,url in sources:
 row={'id':int(id),'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'response bytes at retrieval; not assumed original v1'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence screening'}),timeout=25) as r:
   b=r.read(12*1024*1024+1);assert len(b)<=12*1024*1024
   row.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b),file=id+'.pdf',headers=dict(r.headers));(R/row['file']).write_bytes(b)
 except Exception as e:row['failure']=str(e)
 rows.append(row);(R/'sources.json').write_text(json.dumps(rows,indent=2)+'\n')
 if 'file' in row:
  p=subprocess.run(['pdftotext','-layout',str(R/row['file']),str(R/(id+'.txt'))],capture_output=True,text=True);print(id,p.returncode,p.stderr)
 else:print(id,row['failure'])

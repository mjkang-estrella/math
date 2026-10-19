from pathlib import Path
import urllib.request,subprocess,hashlib,json,concurrent.futures
r=Path(__file__).resolve().parents[1]/'packet/private/primary'
items=['1708.06307v1','1603.05317v2']
def get(n):
 u='https://arxiv.org/pdf/'+n;p=r/(n+'.pdf');b=urllib.request.urlopen(u,timeout=45).read();assert b.startswith(b'%PDF');p.write_bytes(b);out=r/(n+'.txt');v=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True,text=True);return {'id':n,'url':u,'pdf_sha256':hashlib.sha256(b).hexdigest(),'text_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'extraction_exit':v.returncode,'stderr':v.stderr}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(get,items))
(r/'register-extra.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))

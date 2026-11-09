import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).parent;out=[]
for n in ['hayman','abert']:
 p=L/'primary'/(n+'.pdf');m=json.loads(p.with_suffix('.meta.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256'];t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);out.append({'input':str(p),'input_sha256':m['sha256'],'output':str(t),'sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'size':t.stat().st_size,'method':'pdftotext -layout'})
(L/'primary/extractions.json').write_text(json.dumps(out,indent=2)+'\n')

from run import *
import subprocess,sys
for id in ['2607.10449v2','cs/0407059v1']:
 n=id.replace('/','-')+'.pdf';subprocess.run([sys.executable,str(L/'retrieve.py'),'https://arxiv.org/pdf/'+id,n],check=True)
 p=L/'primary'/n
 if p.exists():
  a=sha(p);q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert a==sha(p)
  with (L/'derived.jsonl').open('a') as f:f.write(json.dumps({'source':str(p),'sha256':a,'text':str(q),'text_sha256':sha(q)})+'\n')

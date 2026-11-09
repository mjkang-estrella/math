from run import *
import subprocess,sys
ids=['math/0101009v2','math/0205288v2','math/0210158v1','math/0011220v1','math/0303147v1','math/0009230v1','math/0011170v2','math/0012198v1','math/0209221v1','math/0301199v2','math/0304178v2','math/0107072v1']
for id in ids:
 n=id.replace('/','-')+'.pdf'
 subprocess.run([sys.executable,str(L/'retrieve.py'),'https://arxiv.org/pdf/'+id,n],check=True)
 p=L/'primary'/n
 if p.exists():
  a=sha(p);q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert a==sha(p)
  with (L/'derived.jsonl').open('a') as f:f.write(json.dumps({'source':str(p),'sha256':a,'text':str(q),'text_sha256':sha(q)})+'\n')

from explore import *
ident='1905.00570v1';p=L/'sources'/(ident+'.pdf')
if fetch('https://arxiv.org/pdf/'+ident,p):
 h=digest(p);t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=25);assert h==digest(p)
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(id=ident,pdf=str(p),pdf_sha256=h,text=str(t),text_sha256=digest(t)))+'\n')
 s=t.read_text();print(s[:5500]);i=s.find('Proof');print(s[i:i+4500])

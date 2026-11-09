from research import *
for ident,url in [('1301.6033v2','https://arxiv.org/pdf/1301.6033v2'),('1411.7629v1','https://arxiv.org/pdf/1411.7629v1'),('1503.00325v1','https://arxiv.org/pdf/1503.00325v1'),('roy1997','https://www.numdam.org/item/10.5802/aif.1580.pdf')]:
 p=L/'sources'/(ident+'.pdf')
 if not fetch(url,p):print('FAIL',url);continue
 before=h(p);t=p.with_suffix('.txt');r=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True,timeout=20)
 if r.returncode:print('FAIL EXTRACT',r.stderr);continue
 assert h(p)==before
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(id=ident,pdf=str(p),pdf_sha256=before,text=str(t),text_sha256=h(t)))+'\n')
 s=t.read_text();lines=s.splitlines();print('BODY',ident)
 for i,line in enumerate(lines):
  if any(w in line.lower() for w in ['conjecture','counterexample','log p','log n','zeroes','zeros','converse']):print('\n'.join(lines[max(0,i-1):i+8]))

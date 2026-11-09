import pathlib,subprocess,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*.pdf')):
 if p.read_bytes()[:4]!=b'%PDF':continue
 q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
 out=[]
 for i,l in enumerate(q.read_text().splitlines(),1):
  if re.search(r'conjecture|doi.org|journal-ref',l,re.I):out.append(f'{i}: {l}')
 print(p.name,'\n'+'\n'.join(out[:30]),flush=True)

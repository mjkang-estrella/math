import pathlib,json,re,subprocess
L=pathlib.Path(__file__).resolve().parent
for p in L.glob('*-pdf.body'): subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=15,check=True)
for p in sorted(L.glob('*-pdf.txt')):
 t=p.read_text();print('\n###',p.name)
 lines=t.splitlines()
 for n,line in enumerate(lines):
  if re.search(r'conjecture|open problem',line,re.I):print(n+1,' '.join(lines[max(0,n-1):n+5]))
jobs=[(k+'-head','https://api.github.com/repos/'+r+'/commits/HEAD') for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]]
(L/'registry-jobs.json').write_text(json.dumps(jobs))
for p in sorted(L.glob('*-abs.body')):
 t=p.read_text();print(p.name,re.findall(r'\[v\d+\][\s\S]{0,100}',t))

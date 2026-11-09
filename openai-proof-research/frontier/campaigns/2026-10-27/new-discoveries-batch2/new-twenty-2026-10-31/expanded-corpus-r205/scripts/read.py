import pathlib,subprocess,re,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('pdf-*/body'):
 out=D/'outputs'/('text-'+p.parent.name[4:]+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True)
for p in sorted((D/'outputs').glob('text-*.txt')):
 t=p.read_text(); lines=t.splitlines();print('\n===',p.name,'===')
 for j,l in enumerate(lines):
  if re.search('conjecture|Conjecture',l):print('\n'.join(lines[max(0,j-2):min(len(lines),j+10)]))
for p in (D/'sources').glob('abs-*/body'):
 t=p.read_text();m=re.search(r'Submission history(.*?)</div>',t,re.S)
 print(p.parent.name,re.sub('<[^>]+>',' ',m[1]) if m else 'no history')

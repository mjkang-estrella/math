import pathlib,subprocess,re
D=pathlib.Path(__file__).resolve().parents[1]
for name in ['turan-refined','trees-report']:
 p=D/f'sources/{name}.pdf';q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
 lines=q.read_text().splitlines()
 for i,l in enumerate(lines):
  if re.search(r'Goldschmidt|ex\(2\)|Theorem 7|Lemma 1[12]',l):print(name,i+1,'\n'.join(lines[max(0,i-1):i+8]))

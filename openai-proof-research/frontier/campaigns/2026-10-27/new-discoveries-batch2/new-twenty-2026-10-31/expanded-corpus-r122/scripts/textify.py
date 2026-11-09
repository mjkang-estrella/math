import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*.pdf')):
 q=p.with_suffix('.txt')
 if not q.exists():
  r=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True);print(p.name,r.returncode,r.stderr)

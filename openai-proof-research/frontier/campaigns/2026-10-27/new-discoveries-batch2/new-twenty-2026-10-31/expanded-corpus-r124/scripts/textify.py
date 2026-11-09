import pathlib,subprocess,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*.pdf')):
 if p.read_bytes()[:4]!=b'%PDF':continue
 t=p.with_suffix('.txt')
 r=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True)
 print(p.name,r.returncode,r.stderr,flush=True)

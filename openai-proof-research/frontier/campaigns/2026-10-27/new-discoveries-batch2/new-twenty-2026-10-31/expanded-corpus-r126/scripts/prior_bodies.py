import pathlib,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
for k,u in [('quadrinomials-resolution.pdf','https://arxiv.org/pdf/2203.04216'),('grabner.pdf','https://arxiv.org/pdf/2002.02736')]:print(get((k,u)),flush=True)
for k in ['quadrinomials-resolution','grabner','positroid-resolution']:
 p=D/f'sources/{k}.pdf'
 if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)

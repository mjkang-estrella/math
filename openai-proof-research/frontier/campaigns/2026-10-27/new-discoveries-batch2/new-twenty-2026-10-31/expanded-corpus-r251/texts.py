from pathlib import Path
import subprocess
L=Path(__file__).resolve().parent
for p in (L/'http').glob('*.pdf'):
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)

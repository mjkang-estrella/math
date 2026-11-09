from pathlib import Path
import subprocess
L=Path(__file__).resolve().parent
for p in sorted((L/'sources').glob('*.pdf')):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 print(p.name)

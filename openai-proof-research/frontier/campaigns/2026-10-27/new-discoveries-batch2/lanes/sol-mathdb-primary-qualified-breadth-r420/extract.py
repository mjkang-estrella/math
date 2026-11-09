from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent/'evidence'
for k in ['owr730-pdf','owr742-pdf','owr711-pdf','fano-v2']:
 subprocess.run(['pdftotext','-layout',str(E/(k+'.body')),str(E/(k+'.txt'))],check=True)

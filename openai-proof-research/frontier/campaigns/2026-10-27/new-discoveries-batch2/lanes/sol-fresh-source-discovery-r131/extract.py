import subprocess
from pathlib import Path
L=Path(__file__).resolve().parent
subprocess.run(['pdftotext','-layout',str(L/'sources/journal.pdf'),str(L/'sources/journal.txt')],check=True,timeout=30)

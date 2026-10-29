from pathlib import Path
import subprocess
L=Path(__file__).parent
for i in range(1,8):
 p=L/'inputs'/f'bg2b-{i}'
 subprocess.run(['pdftoppm','-f',str(i),'-l',str(i),'-scale-to','1800','-singlefile','-png',str(L/'inputs/bg2b.pdf'),str(p)],check=True)
 subprocess.run(['tesseract',str(p)+'.png',str(p)],check=True)

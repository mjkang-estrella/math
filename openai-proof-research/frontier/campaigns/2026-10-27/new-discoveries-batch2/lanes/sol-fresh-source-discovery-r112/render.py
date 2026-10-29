from pathlib import Path
import subprocess
L=Path(__file__).parent
for i in [14,15]:
 subprocess.run(['pdftoppm','-f',str(i),'-l',str(i),'-scale-to','2000','-singlefile','-png',str(L/'inputs/bg2a.pdf'),str(L/'inputs'/f'bg2a-{i}')],check=True)

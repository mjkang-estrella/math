from pathlib import Path
import subprocess
E=Path(__file__).parent/'evidence'
p=subprocess.run(['pdftoppm','-scale-to','1300','-png',str(E/'statistical.pdf'),str(E/'statistical-page')],capture_output=True,text=True,timeout=45)
print(p.returncode,p.stderr)

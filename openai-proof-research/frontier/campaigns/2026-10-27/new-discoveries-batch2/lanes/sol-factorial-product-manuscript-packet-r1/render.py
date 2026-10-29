from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parent
D=R/'renders';D.mkdir(exist_ok=True)
subprocess.run(['pdftoppm','-scale-to','1200','-png',str(R/'packet/paper.pdf'),str(D/'paper')],check=True)
for p in [1,31,32,33,49]:
 subprocess.run(['pdftoppm','-f',str(p),'-l',str(p),'-scale-to','1200','-png',str(R/'packet/component/inputs/source.pdf'),str(D/f'source-{p}')],check=True)
(R/'render-receipt.json').write_text(json.dumps({'renderer':subprocess.run(['pdftoppm','-v'],capture_output=True,text=True).stderr,'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.glob('*.png'))},'scope':'all manuscript pages; source title, Theorem4.6 and Problem5.6 pages'},indent=2)+'\n')
print(subprocess.run(['pdfinfo',str(R/'packet/paper.pdf')],capture_output=True,text=True).stdout)

from fetch import get,D
import subprocess
print(get(('composition-later.pdf','https://lipn.fr/~banderier/Papers/Alg.pdf')))
subprocess.run(['pdftotext','-layout',str(D/'sources/composition-later.pdf'),str(D/'sources/composition-later.txt')])

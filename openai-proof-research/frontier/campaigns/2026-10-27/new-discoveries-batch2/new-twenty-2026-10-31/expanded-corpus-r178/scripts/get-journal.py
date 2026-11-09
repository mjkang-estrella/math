import sys,pathlib,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,D
print(fetch('https://publicatio.bibl.u-szeged.hu/37496/2/Leila_orientable_total_dom_1-s2.0-S0166218X25004123-main.pdf','domination2026.pdf'))
subprocess.run(['pdftotext','-layout',str(D/'sources/domination2026.pdf'),str(D/'sources/domination2026.txt')])

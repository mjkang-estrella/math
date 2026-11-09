import sys,pathlib,json,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,D
for a in sys.argv[1:]:
 print(fetch('https://arxiv.org/abs/'+a,a+'.html'),flush=True)
 print(fetch('https://arxiv.org/pdf/'+a,a+'.pdf'),flush=True)
 if (D/'sources'/(a+'.pdf')).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/(a+'.pdf')),str(D/'sources'/(a+'.pdf.txt'))])

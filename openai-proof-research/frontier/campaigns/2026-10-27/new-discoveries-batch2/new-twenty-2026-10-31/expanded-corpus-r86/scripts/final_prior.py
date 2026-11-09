from intake import *
for url,name in [('https://cvgmt.sns.it/media/doc/paper/5962/BNS_CounterExample7d0424.pdf','milnor-counterexample'),('https://arxiv.org/pdf/2608.08193','volume-followup')]:
 if fetch(url,name+'.pdf')==200:subprocess.run(['pdftotext','-layout',str(L/'sources'/(name+'.pdf')),str(L/'sources'/(name+'.txt'))])

from intake import *
if fetch('https://arxiv.org/pdf/1411.6972','billiard-division-prior.pdf')==200:subprocess.run(['pdftotext','-layout',str(L/'sources/billiard-division-prior.pdf'),str(L/'sources/billiard-division-prior.txt')])

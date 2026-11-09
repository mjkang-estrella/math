import pathlib,sys,subprocess,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
for label,url in [('chanpak','https://arxiv.org/pdf/2407.19608'),('carvalho','https://arxiv.org/pdf/2610.04491'),('bisain','https://arxiv.org/pdf/2209.13811')]:
 z=fetch(url,label)
 if z['status']==200:
  p=pathlib.Path(z['body']);subprocess.run(['pdftotext','-layout',str(p),str(p.with_name('text.txt'))])
 print(label,z['status'])

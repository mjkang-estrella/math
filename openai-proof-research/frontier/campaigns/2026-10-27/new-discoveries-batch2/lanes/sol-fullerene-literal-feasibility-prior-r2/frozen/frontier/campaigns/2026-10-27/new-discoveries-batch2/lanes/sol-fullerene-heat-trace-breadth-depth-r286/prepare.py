from pathlib import Path
import sys,tarfile,subprocess,re,runpy
L=Path(__file__).resolve().parent
sys.path.insert(0,str(L));sys.argv=['work','freeze',str(L/'primary/plantri58.tar.gz')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze'];bind=ns['bind']
with tarfile.open(L/'primary/plantri58.tar.gz') as t:
 for m in t.getmembers():
  if m.isfile() and Path(m.name).name in ['fullgen.c','makefile','fullgen-guide.txt','LICENSE-2.0.txt']:
   p=L/'tools'/Path(m.name).name;p.parent.mkdir(exist_ok=True);p.write_bytes(t.extractfile(m).read());bind(p,original=L/'primary/plantri58.tar.gz')
p=freeze(L/'tools/fullgen.c')
for name in ['fullgen-guide.txt','pencil-search.html','cospectral-search.html']:
 p=freeze(L/'primary'/name);s=p.read_text()
 if name.endswith('.html'):
  print(name,re.sub('<[^>]+>',' ',s)[-24000:])
 else:
  for i,line in enumerate(s.splitlines()):
   if re.search('code|stdout|dual|usage|Usage',line):print(i,line)
# metadata navigation for older varied sources
p=freeze(L.parent/'sol-primary-diverse-certifiable-scout-r285/primary/range-problems.html');s=p.read_text()
for block in s.split('<li class="arxiv-result">')[1:]:
 a=re.search(r'arxiv.org/abs/([^"<]+)',block);b=re.search(r'<p class="title is-5 mathjax">(.*?)</p>',block,re.S)
 if a and b:print(a.group(1),re.sub('<[^>]+>','',b.group(1)).strip())

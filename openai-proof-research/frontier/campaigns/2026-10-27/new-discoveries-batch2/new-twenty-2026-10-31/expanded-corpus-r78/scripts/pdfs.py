import sys,subprocess,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
from fetch import get,D
import concurrent.futures
ids=sys.argv[1:]
todo=[(a+'.pdf','https://arxiv.org/pdf/'+a) for a in ids]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo):
  print(v,flush=True)
  p=D/'sources'/v[0]
  if p.exists(): subprocess.run(['pdftotext','-layout',str(p),str(p)[:-4]+'.txt'],timeout=100)

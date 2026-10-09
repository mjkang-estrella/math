"""Retrieve primary literature and preserve exact bytes; no upstream truth audit."""
import urllib.request,pathlib,json,hashlib,concurrent.futures,datetime
from html.parser import HTMLParser
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i07_analysis'
items={'hencl2025':'https://arxiv.org/html/2502.01336v1','pratelli2015':'https://arxiv.org/html/1509.01045v1','faraco_kurylev_ruiz2013':'https://arxiv.org/html/1311.5466v1','rondi2014':'https://arxiv.org/html/1411.1978v1','dm1990':'https://numdam.org/item/AIHPC_1990__7_1_1_0/','fkm_spheres':'https://arxiv.org/html/1006.1957v1'}
class Text(HTMLParser):
 def __init__(self): super().__init__(); self.parts=[]
 def handle_data(self,data):
  if data.strip(): self.parts.append(data.strip())
def get(kv):
 k,u=kv
 try:
  b=urllib.request.urlopen(u,timeout=45).read(); f=S/'literature'/f'{k}.html'; f.parent.mkdir(exist_ok=True); f.write_bytes(b)
  parser=Text(); parser.feed(b.decode()); f.with_suffix('.txt').write_text('\n'.join(parser.parts)+'\n')
  return {'name':k,'url':u,'local':str(f.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'status':'retrieved'}
 except Exception as e: return {'name':k,'url':u,'status':'failed','error':str(e)}
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: out=list(ex.map(get,items.items()))
 (S/'literature-manifest.json').write_text(json.dumps(dict(retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sources=out),indent=2)+'\n')
 for e in out: print(e['name'],e['status'],e.get('bytes',e.get('error')))

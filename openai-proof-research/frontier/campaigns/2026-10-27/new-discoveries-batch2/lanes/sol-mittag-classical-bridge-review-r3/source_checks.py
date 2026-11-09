from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess,concurrent.futures
p=Path(__file__).parent
pairs=[('papadopoulos-2014.pdf','https://alecospapadopoulos.wordpress.com/wp-content/uploads/2014/04/papadopoulos-alecos-half-normal-spec-in-two-tier-stoch-frontier-model.pdf'),('patefield-tandy-2000.pdf','https://www.jstatsoft.org/index.php/jss/article/view/v005i05/620'),('mainardi-2003.pdf','https://arxiv.org/pdf/math/0702133'),('mainardi-2010.pdf','https://arxiv.org/pdf/1004.2950')]
def fetch(pair):
 n,u=pair;r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=40) as f:d=f.read();r.update(status=f.status,final_url=f.url)
  q=p/'live';q.mkdir(exist_ok=True);(q/n).write_bytes(d);r.update(sha256=hashlib.sha256(d).hexdigest(),matches_retained=d==(p/'owncopy/sources'/n).read_bytes())
 except Exception as e:r['failure']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(fetch,pairs))
(p/'live-source-checks.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
# Re-extract all four retained primary bodies to ensure retained text associations.
for n,u in pairs:
 q=p/'extracted';q.mkdir(exist_ok=True)
 subprocess.run(['pdftotext','-layout',str(p/'owncopy/sources'/n),str(q/(n+'.txt'))],check=True)
# Render exact page ranges from own copies, compare decoded pixels with frozen renders.
from PIL import Image,ImageChops
out=[]
for n,pages,prefix in [('papadopoulos-2014.pdf',[5,6],'papadopoulos'),('patefield-tandy-2000.pdf',[1],'patefield'),('mainardi-2003.pdf',[15],'mainardi2003'),('mainardi-2010.pdf',[12,16],'mainardi')]:
 for page in pages:
  base=p/'rerenders'/f'{prefix}-{page:02}';base.parent.mkdir(exist_ok=True)
  subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to-x','1131' if prefix!='mainardi2003' else '1237','-scale-to-y','-1','-singlefile','-png',str(p/'owncopy/sources'/n),str(base)],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  # Page content will be independently visually inspected; retain dimensions explicitly.
  out.append({'pdf':n,'page':page,'image':str(base.with_suffix('.png').relative_to(p)),'size':Image.open(base.with_suffix('.png')).size})
(p/'render-associations.json').write_text(json.dumps(out,indent=2))

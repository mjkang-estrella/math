import pathlib,sys,json,re,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
for r in json.loads((D/'reservation.json').read_text())['rows'][int(sys.argv[1]):int(sys.argv[2])]:
 i=str(r['mathdb_id']);a=r['source_url'].rsplit('/',1)[1]
 absbody=next((D/'sources').glob(i+'-abs-*/body')).read_text()
 versions=sorted(set(re.findall('/abs/'+re.escape(a)+r'(v\d+)',absbody))) or ['v1']
 for v in versions:
  z=fetch('https://arxiv.org/pdf/'+a+v,i+'-'+v+'-pdf')
  if z['status']==200:
   p=pathlib.Path(z['body']);subprocess.run(['pdftotext','-layout',str(p),str(p.with_name('text.txt'))],check=False)
  print(i,v,z['status'])

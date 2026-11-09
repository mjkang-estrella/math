import sys,pathlib,json,re,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out=[]
for z in json.loads((D/'outputs/source-receipts.json').read_text()):
 aid=z['url'].rsplit('/',1)[-1];s=pathlib.Path(z['body']).read_text();vs=sorted(set(re.findall(r'/abs/'+re.escape(aid)+r'v(\d+)',s)),key=int)
 if not vs:vs=['1']
 print(aid,vs,'DOI',re.findall(r'https://doi.org/[^"<>\s]+',s),flush=True)
 for v in vs:
  r=fetch(f'https://arxiv.org/pdf/{aid}v{v}',f'pdf-{aid}v{v}');out.append(r)
  if r['status']==200 and pathlib.Path(r['body']).read_bytes().startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',r['body'],str(D/f'outputs/{aid}v{v}.txt')],check=True)
(D/'outputs/body-receipts.json').write_text(json.dumps(out,indent=2))

import pathlib,sys,json,re,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out={}
for p in sorted((D/'sources').glob('*-abs-*/body')):
 i=p.parent.name.split('-')[0];s=p.read_text(); versions=sorted(set(map(int,re.findall(r'/abs/[0-9.]+v(\d+)',s))));versions=versions or [1]
 doi=re.findall(r'<a[^>]*href="([^"]+)"[^>]*[^>]*>[^<]*',s)
 out[i]={'versions':versions,'doi_links':[x for x in doi if 'doi.org' in x]}
 for v in versions:
  aid=json.loads((D/'extracted.json').read_text())[i]['source_url'].rsplit('/',1)[-1]
  z=fetch(f'https://arxiv.org/pdf/{aid}v{v}',i+f'-v{v}-pdf');out[i][str(v)]=z
  if z['status']==200 and pathlib.Path(z['body']).read_bytes().startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',z['body'],str(D/'outputs'/f'{i}-v{v}.txt')],check=True)
(D/'outputs/source-versions.json').write_text(json.dumps(out,indent=2))

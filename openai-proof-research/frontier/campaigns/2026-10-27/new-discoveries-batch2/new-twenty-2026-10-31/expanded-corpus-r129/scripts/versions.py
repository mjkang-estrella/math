import pathlib,json,re,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'scripts'))
from fetch import get
from concurrent.futures import ThreadPoolExecutor
xs=json.loads((D/'extracted.json').read_text()); versions={}
for o in xs.values():
 a=o['source_url'].rsplit('/',1)[-1]; t=(D/'sources'/f'{a}.html').read_text(); v=sorted(set(re.findall(r'\[v(\d+)\]',t)),key=int)
 versions[a]=v
print(versions,flush=True)
(D/'outputs/versions.json').write_text(json.dumps(versions,indent=2))
with ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(get,[(f'{a}v{v}.pdf',f'https://arxiv.org/pdf/{a}v{v}') for a,vs in versions.items() for v in vs]):print(x,flush=True)
for p in sorted((D/'sources').glob('*.pdf')):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)

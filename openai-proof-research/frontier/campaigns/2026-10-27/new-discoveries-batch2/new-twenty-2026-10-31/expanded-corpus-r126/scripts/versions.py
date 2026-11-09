import pathlib,re,json,sys,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'))
from fetch import get
vs={}
for p in sorted((D/'sources').glob('*.abs.html')):
 a=p.name[:-9];t=p.read_text(); h=t.split('Submission history')[1].split('</div>')[0];v=sorted(set(map(int,re.findall(r'\[v(\d+)\]',h))))
 vs[a]=v;print(a,v,flush=True)
(D/'outputs/versions.json').write_text(json.dumps(vs,indent=2)+'\n')
todo=[(f'{a}v{v}.pdf',f'https://arxiv.org/pdf/{a}v{v}') for a,versions in vs.items() for v in versions]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo): print(r,flush=True)

import pathlib,json,sys,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
root=json.loads((D/'sources/omega-root.json').read_text());todo=[]
for x in root['tree']:
 if x['path'] in ('D5','Problems'):todo.append(('omega-'+x['path']+'.json',x['url']+'?recursive=1'))
todo += [('lv-release.html','https://www.evidencepress.org/releases/lotka-volterra-tree-presentations/'),('bickel-hong.html','https://arxiv.org/html/2506.12624'),('theta-published.html','https://academic.oup.com/imrn/article/2025/21/rnaf332/8306701')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(get,todo):print(x,flush=True)

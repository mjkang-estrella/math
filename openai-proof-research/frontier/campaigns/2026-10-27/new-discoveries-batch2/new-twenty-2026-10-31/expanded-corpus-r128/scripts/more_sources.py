import pathlib,json,importlib.util,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']
todo=[('omega-mesh-'+v['path'].split('/')[-1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/D5/'+v['path']) for v in json.loads((D/'outputs/registry-D5-hits.json').read_text()) if 'MeshPatternS21' in v['path']]
todo += [('wreath-journal.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p44/pdf/'),('mesh-public.html','https://www.trureturing.org/research/lv-zhang-mesh-123-321-joint-symmetry/')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(f.get,todo):print(r,flush=True)

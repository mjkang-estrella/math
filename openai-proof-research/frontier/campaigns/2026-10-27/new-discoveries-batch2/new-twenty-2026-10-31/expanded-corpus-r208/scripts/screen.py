import pathlib,json,importlib.util,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
root=json.loads((D/'sources/omega-root.json').read_text())
for x in root['tree']:
 if x['path'] in ['D5','Problems']:h.get('omega-'+x['path']+'-complete.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1')
j=json.loads((D/'sources/leanpool-tree.json').read_text())
for x in j['tree']:
 if x['path'].startswith('candidates/') and x['type']=='blob':h.get('leanpool-candidate-'+x['path'].split('/')[-1],'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+x['path'])
for ix,q in enumerate(['"2412.17391" lean','"2411.14308" lean','"2301.05202" lean','"2410.23009" lean','"382314" lean','"358735" lean']):
 if 'api.github.com' in h.denied:break
 h.get('github-search-'+str(ix)+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q));time.sleep(8)

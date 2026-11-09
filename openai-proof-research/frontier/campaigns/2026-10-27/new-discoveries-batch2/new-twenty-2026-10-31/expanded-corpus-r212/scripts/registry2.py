import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
J=json.loads((D/'sources/omega-tree.json').read_text())
for p in ['D5','Problems']:
 a=next((x for x in J['tree'] if x['path']==p),None)
 print(p,a)
 if a:subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),'omega-'+p+'.json',a['url']+'?recursive=1'])

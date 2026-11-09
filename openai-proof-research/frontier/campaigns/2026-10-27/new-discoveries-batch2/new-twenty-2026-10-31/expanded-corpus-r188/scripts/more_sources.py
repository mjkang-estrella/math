import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
tree=json.loads((D/'sources/omega-tree.body').read_text());args=[]
for x in tree['tree']:
 if x['path'] in ['D5','Problems']:args+=['omega-'+x['path'],x['url']+'?recursive=1']
for i,v in json.loads((D/'outputs/version-inventory.json').read_text()).items():
 for j,doi in enumerate(v['doi']):args += [i+'-vor-doi-'+str(j),'https://doi.org/'+doi]
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*args])

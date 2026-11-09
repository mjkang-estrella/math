import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'))
from fetch import fetch
D=pathlib.Path(sys.argv[1]);data=json.loads((D/'extracted.json').read_text())
for i,o in data.items():
 s=(D/'sources'/('abs-'+i)/'body').read_text(); versions=sorted(set(re.findall(r'\[v(\d+)\]',s)))
 for v in versions:fetch(o['source_url'].replace('/abs/','/html/')+'v'+v,'html-'+i+'v'+v)

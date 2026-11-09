import json,pathlib,re,sys
O=pathlib.Path(__file__).parent
rs=json.loads((O/'selected-records.json').read_text())
for r in rs[int(sys.argv[1]):int(sys.argv[2])]:
 p=O/'primary'/(r['source_url'].rsplit('/',1)[1]+'.txt'); pages=p.read_text().split('\f'); n=int(re.search(r'page (\d+)',r['references']).group(1));t=pages[n-1]
 print('\nID',r['mathdb_id'],'page',n,'\n',t)

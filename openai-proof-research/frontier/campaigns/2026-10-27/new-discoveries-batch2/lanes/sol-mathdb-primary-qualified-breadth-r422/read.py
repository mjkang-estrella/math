import json,pathlib,sys
O=pathlib.Path(__file__).parent
rs=json.loads((O/'selected-records.json').read_text())
for r in rs[int(sys.argv[1]):int(sys.argv[2])]:
 print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],'\nREF',r['references'],'\nSOL',r['solutions'])

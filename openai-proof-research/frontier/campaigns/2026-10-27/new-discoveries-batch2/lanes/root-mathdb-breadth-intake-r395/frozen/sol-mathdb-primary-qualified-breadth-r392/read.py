import json,pathlib,sys
p=pathlib.Path(__file__).parent
for r in json.loads((p/'records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_url'],'\n'+r['statement'])

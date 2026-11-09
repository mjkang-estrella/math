import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for a in json.loads((P/'assigned-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 print('\nID',a['mathdb_id'],a['record']['source_url']);print(a['statement'])

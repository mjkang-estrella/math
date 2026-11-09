import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
rows=json.loads((P/'assigned-records.json').read_text())
for i,a in enumerate(rows):
 if int(sys.argv[1])<=i<int(sys.argv[2]):print('\n',i,a['mathdb_id'],a['record']['source_url'],'\n',a['statement'])

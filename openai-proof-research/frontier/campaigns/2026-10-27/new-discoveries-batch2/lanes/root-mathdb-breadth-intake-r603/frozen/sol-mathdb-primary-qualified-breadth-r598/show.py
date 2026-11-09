import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for r in json.loads((P/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:print('\nID',r['mathdb_id'],r['record']['title'],'\n'+r['statement']+'\nSOURCE '+str(r['record']['source_url']))

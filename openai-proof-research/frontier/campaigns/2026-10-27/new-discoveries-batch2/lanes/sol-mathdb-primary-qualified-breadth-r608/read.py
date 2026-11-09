import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for x in json.loads((P/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record']; print('\nID',x['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],r['references'])

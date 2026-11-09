import json,pathlib,sys
L=pathlib.Path(__file__).resolve().parent
for x in json.loads((L/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url']))

import json,pathlib,sys
D=pathlib.Path(__file__).resolve().parent
for e in json.loads((D/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=e['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r.get('source_url'),r.get('source_name'))

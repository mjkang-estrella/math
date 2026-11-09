import json,pathlib,sys
O=pathlib.Path(__file__).resolve().parent
rows=json.loads((O/'literal-records.json').read_text())
for x in rows[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_name'],r['source_url'],'\n'+r['statement'])

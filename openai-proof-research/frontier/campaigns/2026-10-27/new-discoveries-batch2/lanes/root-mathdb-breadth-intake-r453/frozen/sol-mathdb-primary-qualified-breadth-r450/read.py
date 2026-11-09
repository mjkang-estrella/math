import json,pathlib
L=pathlib.Path(__file__).resolve().parent
for x in json.loads((L/'assigned-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_name'],r['source_url'],'\n')

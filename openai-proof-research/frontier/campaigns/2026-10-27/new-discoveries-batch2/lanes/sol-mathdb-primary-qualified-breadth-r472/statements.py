import json,pathlib
L=pathlib.Path(__file__).resolve().parent
for e in json.loads((L/'assigned-records.json').read_text()):
 r=e['record'];print('\nID',r['mathdb_id'],r['source_url'],'\n',r['statement'])

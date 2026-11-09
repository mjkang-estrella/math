import json,pathlib
for x in json.loads((pathlib.Path(__file__).parent/'selected-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_name'],r['source_url'],'\n'+r['statement'])

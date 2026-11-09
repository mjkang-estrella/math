import json,pathlib
P=pathlib.Path(__file__).resolve().parent
for x in json.loads((P/'literal-records.json').read_text()):
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'])

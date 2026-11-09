import json,pathlib
P=pathlib.Path(__file__).parent
for x in json.loads((P/'literal-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['title'],'\n',r['statement'],'\n')

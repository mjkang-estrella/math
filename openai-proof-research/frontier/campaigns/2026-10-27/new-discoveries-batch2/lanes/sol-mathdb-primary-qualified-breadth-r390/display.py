import json,pathlib
for x in json.loads((pathlib.Path(__file__).parent/'statements.json').read_text()):
 r=x['record'];print(str(r['mathdb_id'])+' '+r['statement']+'\nSOURCE '+r['source_url']+'\n')

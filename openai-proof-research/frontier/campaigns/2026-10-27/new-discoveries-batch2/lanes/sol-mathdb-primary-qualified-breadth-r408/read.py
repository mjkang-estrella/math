import json,pathlib
L=pathlib.Path(__file__).resolve().parent
for x in json.loads((L/'records.json').read_text()):
 r=x['record'];print('\n',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],'DOC',r['documented_by_source_url'])

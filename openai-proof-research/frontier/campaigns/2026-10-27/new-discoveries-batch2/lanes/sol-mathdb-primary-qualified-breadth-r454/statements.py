import pathlib,json
L=pathlib.Path(__file__).resolve().parent
for x in json.loads((L/'assigned-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['statement'],'\nSOURCE:',r['source_url'],r['source_name'],'\n')

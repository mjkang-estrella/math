import json,pathlib,sys
a=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for x in a[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\n',r['mathdb_id'],r['title'],'\n',r['statement'],'\n',r['source_url'])

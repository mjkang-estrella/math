import json,pathlib,sys
rs=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for x in rs[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\n',r['mathdb_id'],r['source_url'],'\n',r['statement'])

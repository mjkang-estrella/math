import json,pathlib,sys
rs=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for e in rs[int(sys.argv[1]):int(sys.argv[2])]:
 r=e['record'];print('\n',r['mathdb_id'],r['title'],'\n',r['statement'],'\n',r['source_url'])

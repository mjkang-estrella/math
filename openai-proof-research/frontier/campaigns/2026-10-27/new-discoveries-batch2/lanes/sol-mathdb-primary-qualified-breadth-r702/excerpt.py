import json,pathlib,sys
x=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for e in x[int(sys.argv[1]):int(sys.argv[2])]:
 r=e['record'];print('\nID',r['mathdb_id'],r['title'],'SOURCE',r['source_url']);print(r['statement'])

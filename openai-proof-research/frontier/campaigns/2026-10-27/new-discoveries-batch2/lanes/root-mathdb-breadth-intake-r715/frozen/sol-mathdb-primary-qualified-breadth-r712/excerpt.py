import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for e in json.loads((P/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=e['record'];print(r['mathdb_id'],r['source_url']);print(r['statement'])

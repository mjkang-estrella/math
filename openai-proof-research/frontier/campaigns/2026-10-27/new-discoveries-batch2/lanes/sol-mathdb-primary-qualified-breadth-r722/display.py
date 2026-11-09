import json,pathlib,sys
r=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for x in r[int(sys.argv[1]):int(sys.argv[2])]:
 z=x['record'];print(z['mathdb_id'],z['source_url'],z['statement'],'\n')

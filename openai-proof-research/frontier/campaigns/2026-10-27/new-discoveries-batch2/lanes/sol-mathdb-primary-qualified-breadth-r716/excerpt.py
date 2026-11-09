import json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for d in sorted(json.loads((P/'literal-records.json').read_text()),key=lambda d:d['mathdb_id'])[int(sys.argv[1]):int(sys.argv[2])]:
 r=d['record'];print(str(r['mathdb_id'])+' '+r['source_url']+'\n'+r['statement']+'\n')

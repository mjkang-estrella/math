import json,pathlib,sys
P=pathlib.Path(__file__).parent
for i,x in enumerate(json.loads((P/'literal-records.json').read_text())):
 if int(sys.argv[1])<=i<int(sys.argv[2]):
  r=x['record'];print(r['mathdb_id'],r['statement'],'SOURCE',r['source_url'],'\n')

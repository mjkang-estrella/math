import pathlib,json,sys
L=pathlib.Path(__file__).resolve().parent
v=json.loads((L/'literal-records.json').read_text())
for x in v[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print(r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url']))

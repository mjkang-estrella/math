import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parent
rows=json.loads((D/'assigned-records.json').read_text())
for x in rows[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\n',r['mathdb_id'],r['source_url'],'\n'+r['statement'])

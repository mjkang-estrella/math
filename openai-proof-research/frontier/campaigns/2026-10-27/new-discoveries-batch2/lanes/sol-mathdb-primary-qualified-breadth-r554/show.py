import pathlib,json,sys
P=pathlib.Path(__file__).parent
for y in json.loads((P/'assigned-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=y['record'];print('\nID',r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url']))

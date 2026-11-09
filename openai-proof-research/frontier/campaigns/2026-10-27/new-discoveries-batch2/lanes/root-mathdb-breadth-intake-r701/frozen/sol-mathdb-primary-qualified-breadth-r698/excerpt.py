import pathlib,json,sys
P=pathlib.Path(__file__).parent
for x in json.loads((P/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print(r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url'])+'\n')

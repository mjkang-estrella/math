import json,pathlib,sys
O=pathlib.Path(__file__).parent
for x in json.loads((O/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print(x['id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'])

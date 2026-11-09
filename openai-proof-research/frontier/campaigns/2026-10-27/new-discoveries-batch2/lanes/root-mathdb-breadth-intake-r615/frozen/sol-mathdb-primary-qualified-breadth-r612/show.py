import json,pathlib,sys
rows=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for x in rows[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record'];print('\n',r['mathdb_id'],r['title'],'FLAG',r['statement_completeness'],'\n',r['statement'],'\nSOURCE',r['source_url'])

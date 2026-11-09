import pathlib,json,sys
rs=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for d in rs[int(sys.argv[1]):int(sys.argv[2])]:print('\n',d['mathdb_id'],d['record']['title'],'\n',d['statement'],'\nSOURCE',d['record']['source_url'])

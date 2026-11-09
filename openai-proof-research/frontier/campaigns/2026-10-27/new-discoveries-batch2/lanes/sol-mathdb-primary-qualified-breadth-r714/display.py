import pathlib,json,sys
P=pathlib.Path(__file__).parent
for x in json.loads((P/'literal-records.json').read_text())[int(sys.argv[1]):int(sys.argv[2])]:print(x['id'],x['record']['source_url'],'\n',x['record']['statement'],'\n')

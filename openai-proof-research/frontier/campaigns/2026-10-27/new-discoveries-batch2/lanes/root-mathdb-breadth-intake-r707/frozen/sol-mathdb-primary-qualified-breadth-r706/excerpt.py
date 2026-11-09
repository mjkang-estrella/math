import json,sys,pathlib
r=json.loads((pathlib.Path(__file__).parent/'literal-records.json').read_text())
for x in r[int(sys.argv[1]):int(sys.argv[2])]:print(str(x['mathdb_id'])+' '+x['record']['title']+'\n'+x['record']['statement']+'\nSOURCE '+str(x['record']['source_url'])+'\n')

import json,pathlib
O=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((O/'statements.json').read_text()); s='\n\n'.join(str(x['record']['mathdb_id'])+' '+x['record']['title']+'\n'+x['record']['statement']+'\nSOURCE '+str(x['record']['source_url']) for x in rows);(O/'statements-read.txt').write_text(s+'\n');print(s)

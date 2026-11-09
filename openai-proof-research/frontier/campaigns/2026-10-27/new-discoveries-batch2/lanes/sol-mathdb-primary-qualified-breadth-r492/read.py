from pathlib import Path
import json
D=Path(__file__).parent
s='\n\n'.join(str(x['record']['mathdb_id'])+' '+x['record']['title']+'\n'+x['record']['statement']+'\nSOURCE '+str(x['record'].get('source_url'))+'\nREFERENCES '+str(x['record'].get('references')) for x in json.loads((D/'assigned-records.json').read_text()))
(D/'literal-reading.txt').write_text(s+'\n')
print(s)

from pathlib import Path
import json
R=Path(__file__).resolve().parent
s='\n\n'.join(str(x['mathdb_id'])+' '+x['title']+'\n'+x['statement']+'\nSOURCE '+x['source_url'] for x in json.loads((R/'records.json').read_text()))
(R/'literal-reading.txt').write_text(s);print(s)

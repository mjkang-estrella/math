from pathlib import Path
import json
P=Path(__file__).resolve().parent
for d in json.loads((P/'assigned-records.json').read_text()):
 print('\nID',d['mathdb_id'],d['record'].get('title'),'LINE',d['corpus_line']);print(d['statement_utf8']);print('SOURCE',json.dumps({k:v for k,v in d['record'].items() if k not in ['statement','solutions','tags']},ensure_ascii=False))

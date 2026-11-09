import json,pathlib
P=pathlib.Path(__file__).resolve().parent
for a in json.loads((P/'assigned-records.json').read_text()):
 r=a['record'];print('\nID',a['mathdb_id'],r.get('title'));print(a['statement']);print('SOURCES',json.dumps({k:v for k,v in r.items() if k not in ['statement','solutions','tags']},ensure_ascii=False))

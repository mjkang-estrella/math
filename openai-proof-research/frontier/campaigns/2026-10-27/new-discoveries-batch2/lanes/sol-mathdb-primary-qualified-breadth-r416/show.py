import json,pathlib
L=pathlib.Path(__file__).parent
for item in json.loads((L/'records.json').read_text()):
 x=item['record'];print('\nID',x['mathdb_id'],x['title']);print(x['statement']);print('SOURCE',x['source_name'],x['source_url']);print('REF',x['references'],'SOL',x['solutions'])

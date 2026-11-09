import json,pathlib
for x in json.loads((pathlib.Path(__file__).parent/'records.json').read_text()):print(str(x['mathdb_id'])+' '+x['statement'])

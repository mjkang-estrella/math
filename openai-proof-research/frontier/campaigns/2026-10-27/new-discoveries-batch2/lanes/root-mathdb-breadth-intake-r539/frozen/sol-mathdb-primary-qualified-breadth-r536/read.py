import sys
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
rows=json.loads((P/'assigned-records.json').read_text())
for i,r in enumerate(rows):
 if len(sys.argv)>1 and not int(sys.argv[1])<=i+1<=int(sys.argv[2]):continue
 print('\n###',i+1,r['mathdb_id'],r['record']['title']);print(r['statement']);print('META', {k:v for k,v in r['record'].items() if 'source' in k or 'reference' in k})

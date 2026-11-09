import json,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r597'
for name in ['active-breadth-reservations.json']:
 d=json.loads((I/name).read_text());print([(x.keys(),len(x.get('ids',[])),x.get('lane')) for x in d])
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 d=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());print(name, str(d)[:1000])

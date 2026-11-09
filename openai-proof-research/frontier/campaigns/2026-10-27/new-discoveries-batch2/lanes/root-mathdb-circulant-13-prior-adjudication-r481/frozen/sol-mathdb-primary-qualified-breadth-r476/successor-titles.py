import json,pathlib
D=pathlib.Path(__file__).resolve().parent
for line in (D/'successor-access.jsonl').read_text().splitlines():
 r=json.loads(line);print(r['mathdb_id'],r['status'])
 for e in r.get('entries',[]):print(e['id'],e['title'].replace('\n',' '))

exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('for n in [')[0])
a=j(P/'assigned-records.json')
for x in a:
 r=x['record'];print(x['mathdb_id'],r['title'],r['source_url'],json.dumps(r['references'],ensure_ascii=False))
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 d=j(L/'root-mathdb-accepted-exclusions-r304'/n)
 print(n,json.dumps(d,ensure_ascii=False)[:24000])

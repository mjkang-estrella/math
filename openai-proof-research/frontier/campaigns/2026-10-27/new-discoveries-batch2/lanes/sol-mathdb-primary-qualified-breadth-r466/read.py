import pathlib,json
L=pathlib.Path(__file__).resolve().parent
for a in json.loads((L/'assigned-records.json').read_text()):
 r=a['record']; print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],'REFS',r['references'])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 print(n,(L.parent/'root-mathdb-accepted-exclusions-r304'/n).read_text())
print('CAYLEY',(L.parent/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
for n in ['ledger.json','prior-campaign-context.json']:
 p=L.parent.parent/n; print(n,p.read_text()[:16000])
print('COVERAGE SCHEMA',str(json.loads((L.parent/'root-mathdb-breadth-intake-r465/coverage-delta.json').read_text()))[:2500])

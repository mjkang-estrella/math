import json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/registry-screen.json').read_text())
print('HEADS',[(k,v.get('sha')) for k,v in r['heads'].items()]);print('pool hits',r['hits']);print('queries',[(x['query'],x['status']) for x in r['queries']])
for p,hits in r['path_hits'].items():
 print(p,'hits',len(hits));print('\n'.join(x['path'] for x in hits if re.search('dominat|orientab|pebbling|cochord|subtraction|cube.width|upcycle',x['path'],re.I)))

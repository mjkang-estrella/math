import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
for f in [L.parents[1]/'ledger.json',L.parent/'ledger.json',L.parents[1]/'prior-campaign-context.json']:
 o=json.loads(f.read_text()); print(str(f),hashlib.sha256(f.read_bytes()).hexdigest()); print('keys',list(o)); (L/'outputs'/('read-'+f.name)).write_text(json.dumps(o,indent=2))
for i,v in json.loads((L/'outputs/provenance.json').read_text()).items():
 o=v['record']; print('\n',i,o['title'],'\n',o['statement'])

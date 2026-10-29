import json,hashlib,sys,time
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
if sys.argv[1]=='freeze':
 originals=[R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-fresh-screen'/x for x in ['SCREENING.md','subsum-screen.json','screen_subsum.py']]
 for folder in ['sol-fresh-discrete-discovery-r6','sol-denominator-dyadic-discovery-r1','sol-fresh-discrete-algebra-r23','sol-fresh-source-discovery-r63','sol-fresh-source-discovery-r64','sol-fresh-source-discovery-r75']:
  originals.append(B/'lanes'/folder/'discovery.md')
 receipts=[]
 for i,p in enumerate(originals):
  data=p.read_bytes();dest=L/'sources'/('original-%02d'%i+p.suffix);dest.write_bytes(data)
  receipts.append({'original':str(p),'copy':str(dest.relative_to(L)),'sha256':sha(data),'bytes':len(data),'as_read_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
 (L/'original-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
 scientific=[]
 for p in sorted((L/'sources').iterdir()):
  if not p.name.startswith('context-'):
   data=p.read_bytes();scientific.append({'path':str(p.relative_to(L)),'sha256':sha(data),'bytes':len(data)})
 (L/'scientific-freeze.json').write_text(json.dumps(scientific,indent=2)+'\n')
 print('scientific freeze',len(scientific))
elif sys.argv[1]=='seal':
 entries=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in ['finalmanifest.json','manifest-verification.json','seal.log']:
   data=p.read_bytes();entries.append({'path':str(p.relative_to(L)),'bytes':len(data),'sha256':sha(data)})
 (L/'finalmanifest.json').write_text(json.dumps(entries,indent=2)+'\n')
 print('sealed',len(entries))
elif sys.argv[1]=='verify':
 data=(L/'finalmanifest.json').read_bytes();entries=json.loads(data)
 excluded={'finalmanifest.json','manifest-verification.json','seal.log'}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in excluded}
 assert actual=={r['path'] for r in entries}
 assert {'SUMMARY.md','discovery.md','progress.md','provenance.json','http.jsonl','scientific-freeze.json','checks.py','run-check.sh','check-results.json'}<=actual
 for r in entries:
  b=(L/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'],r['path']
 assert not (L/'PROOF.md').exists()
 receipt={'status':'PASS','entries':len(entries),'manifest_sha256':sha(data),'verified_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'excluded_from_manifest':['finalmanifest.json','manifest-verification.json','seal.log']}
 (L/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)

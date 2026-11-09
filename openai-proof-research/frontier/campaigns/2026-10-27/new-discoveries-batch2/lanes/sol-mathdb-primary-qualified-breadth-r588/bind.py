import pathlib,hashlib,json,datetime
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); L=B/'lanes'; I=L/'root-mathdb-breadth-intake-r587'; O=L/'sol-mathdb-primary-qualified-breadth-r588'
def rec(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
names=['manifest.json','queue.json','reserved-ids.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','bindings.json','active-breadth-reservations.json']
(O/'initial-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[rec(I/n) for n in names]},indent=2)+'\n')
for n in ['manifest.json','bindings.json','queue.json','reserved-ids.json','active-breadth-reservations.json']:
 print('\nFILE',n);print((I/n).read_text())

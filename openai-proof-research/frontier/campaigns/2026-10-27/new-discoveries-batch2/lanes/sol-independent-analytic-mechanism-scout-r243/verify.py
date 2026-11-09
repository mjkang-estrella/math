import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=[];checked=0
def check(p,want):
 global checked
 checked+=1
 if not p.is_file() or h(p)!=want:fail.append(str(p))
manifest=L/'manifest.json';m=json.loads(manifest.read_text())
for name,digest in m.items():check(L/name,digest)
for r in json.loads((L/'source-map.json').read_text()):
 for key in ['original','copy']:check(L/r[key],r['sha256'])
 check(L/r['text'],r['text_sha256'])
for r in json.loads((L/'freeze.json').read_text()):
 check(pathlib.Path(r['original']),r['sha256']);check(L/r['copy'],r['sha256'])
for n in ['history-screen-initial.json','history-screen.json']:
 for r in json.loads((L/n).read_text())['references']:check(pathlib.Path(r['path']),r['sha256'])
c=json.loads((L/'catalogue-screen.json').read_text());check(pathlib.Path(c['path']),c['sha256'])
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checked,'failures':fail,'pass':not fail,'manifest_sha256':h(manifest),'counts_unchanged':'9 additional /39 total /next40','scope':'hash integrity only; no mathematical proof certification'}
(L/'receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));sys.exit(bool(fail))

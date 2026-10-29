import pathlib, hashlib, json, sys, datetime, shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent
S=B/'sol-fresh-source-discovery-r111'
R=B/'root-renyi-threshold-review-freeze-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''): h.update(b)
 return h.hexdigest()
manifest=json.loads((R/'review-freeze.json').read_text())
rows=[]
for name,want in manifest.items():
 p=S/name
 got=sha(p)
 rows.append(dict(path=str(p),bytes=p.stat().st_size,expected=want,actual=got,match=want==got))
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(rows),'all_match':all(x['match'] for x in rows),'files':rows,'guard_sha256':sha(B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')}
(L/(sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2)+'\n')
assert out['all_match']
if sys.argv[1]=='before':
 for name in ['PROOF.md','SUMMARY.md','provenance.json','screen-receipt.json','exact_checks.py','exact-checks.jsonl','source-receipts.jsonl','sources/reverse.txt','sources/reverse.pdf','sources/melbourne-tkocz.txt','sources/melbourne-tkocz.pdf']:
  dst=L/'inputs'/name; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(S/name,dst)
 for name in ['review-freeze.json','ADOPTION.json','primary-receipts.json','arxiv-abstract.html','arxiv-v3.html','unstaged-bulk-evidence.json']:
  dst=L/'inputs/root'/name; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(R/name,dst)
print(json.dumps({k:v for k,v in out.items() if k!='files'}))

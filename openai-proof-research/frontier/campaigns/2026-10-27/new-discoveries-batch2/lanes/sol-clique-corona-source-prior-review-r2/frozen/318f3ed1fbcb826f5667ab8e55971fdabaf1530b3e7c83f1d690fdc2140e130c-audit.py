import pathlib,json,hashlib,datetime,shutil,sys
L=pathlib.Path(__file__).parent
B=L.parent.parent
F=B/'lanes/root-r168-preliminary-freeze-r1/review-freeze.json'
def sha(b):return hashlib.sha256(b).hexdigest()
rows=json.loads(F.read_text())['files']
out=[]
for r in rows:
 p=pathlib.Path(r['path']); b=p.read_bytes()
 assert len(b)==r['bytes'] and sha(b)==r['sha256'],str(p)
 q=L/'copies'/p.relative_to(B/'lanes/sol-fresh-source-discovery-r168')
 if sys.argv[1]=='before':
  q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 assert q.read_bytes()==b
 out.append(dict(r,copy=str(q),copy_sha256=sha(q.read_bytes())))
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'phase':sys.argv[1],'count':len(out),'all_match':True,'freeze_sha256':sha(F.read_bytes()),'files':out}
(L/(sys.argv[1]+'-freeze.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='files'}))

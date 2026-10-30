import pathlib,json,hashlib,sys,datetime
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
R=B/'lanes/sol-kazemi-hypercube-preliminary-review-r1'
F=B/'lanes/root-r152-preliminary-freeze-r1/review-freeze.json'
freeze=json.loads(F.read_text()); rows=[]
assert len(freeze['files'])==34
for x in freeze['files']:
 p=pathlib.Path(x['path']); data=p.read_bytes(); h=hashlib.sha256(data).hexdigest()
 assert p.is_absolute() and h==x['sha256'] and len(data)==x['bytes'],str(p)
 dest=R/'frozen'/p.relative_to(freeze['root'])
 if sys.argv[1]=='before':
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 assert dest.read_bytes()==data
 rows.append(dict(x,copy=str(dest),verified=True))
(R/('freeze-'+sys.argv[1]+'.json')).write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(F.read_bytes()).hexdigest(),'files':rows},indent=2)+'\n')
print(sys.argv[1],len(rows),'original and private-copy hashes verified')

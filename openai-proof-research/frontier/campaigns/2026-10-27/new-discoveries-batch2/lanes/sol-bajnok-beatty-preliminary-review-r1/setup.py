import pathlib,json,hashlib,shutil,datetime
D=pathlib.Path(__file__).resolve().parent; B=D.parent.parent
F=B/'lanes/root-bajnok-beatty-review-freeze-r1/review-freeze.json'; f=json.loads(F.read_text()); S=pathlib.Path(f['source_lane']); rows=[]
for name,h in f['files'].items():
 b=(S/name).read_bytes(); actual=hashlib.sha256(b).hexdigest(); assert actual==h,(name,actual,h)
 out=D/'copy'/name;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b);rows.append({'path':name,'sha256':actual})
(D/'freeze-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified':len(rows),'files':rows},indent=2))
for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 shutil.copyfile(B/n,D/('context-'+n))

import pathlib,json,hashlib
p=pathlib.Path(__file__).parent;b=p.parent.parent
r={}
for f in [b/'ledger.json',b/'prior-campaign-context.json']:
 d=json.loads(f.read_text());r[str(f)]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'keys':list(d),'accepted':[{k:x.get(k) for k in ['number','title','scope','source_target']} for x in d.get('accepted',[])]}
c=json.loads((p.parent/'sol-fresh-source-discovery-r83/sources/omega-compare.json').read_text());r['baseline_compare']={k:c.get(k) for k in ['status','ahead_by','behind_by','total_commits']};r['baseline_compare']['files']=[x['filename'] for x in c.get('files',[])];r['baseline_compare']['file_count']=len(c.get('files',[]))
for lane in ['sol-fresh-source-discovery-r85','sol-fresh-source-discovery-r86']:
 r[lane]={};f=p.parent/lane/'http.json'
 if f.exists():r[lane]['urls']=[x.get('url') for x in json.loads(f.read_text())]
 for n in ['progress.md','SUMMARY.md','discovery.md']:
  f=p.parent/lane/n
  if f.exists():r[lane][n]=f.read_text()
(p/'context.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2)[:28000])

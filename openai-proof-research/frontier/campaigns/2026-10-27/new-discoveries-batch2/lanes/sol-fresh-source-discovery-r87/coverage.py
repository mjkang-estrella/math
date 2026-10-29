import pathlib,json,hashlib,datetime
p=pathlib.Path(__file__).parent;b=p.parent.parent;out={}
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((b/n).read_text());v={}
 for k in ['candidates','excluded','held_candidates']:
  x=d.get(k,[]);v[k]=x
 out[n]=v
c=json.loads((p.parent/'sol-fresh-source-discovery-r83/sources/omega-compare.json').read_text());q=json.loads((p/'sources/omega-delta.json').read_text())
out['coverage']={'baseline':{'omega_head':'1b999d9fda71df7537b62327147496d64a6f66ef','omega_claimed_paths':350197,'openai_head':json.loads((p/'sources/openai-head.json').read_text())['sha'],'checked_current_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_files':{}},'r83_compare':{k:c.get(k) for k in ['status','ahead_by','behind_by','total_commits']},'r83_compare_files':len(c.get('files',[])),'current_delta':{k:q.get(k) for k in ['status','ahead_by','behind_by','total_commits']},'current_delta_files':[x['filename'] for x in q.get('files',[])],'limits':['Compare API file lists can truncate; no claim that compare metadata is a complete updated recursive tree.','Baseline complete-tree receipt inherited from root; raw tree paths screened locally, selected primary mathematical bodies separately read.','Filename absence alone supplies no priority clearance.','Machina data snapshot is 2026-09-09, not a current universal registry.','No exhaustive MathSciNet/zbMATH, non-English or all-body screen.']}
for n in ['omega-tree.txt','openai-tree.txt']:
 f=p.parent/'root-edge-irregulator-final-freeze-r1'/n;out['coverage']['baseline']['baseline_files'][n]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'lines':sum(1 for _ in f.open())}
(p/'coverage.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:18000])

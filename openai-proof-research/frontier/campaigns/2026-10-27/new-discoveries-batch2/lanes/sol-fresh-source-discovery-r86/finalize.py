import pathlib,json,datetime,hashlib,re
P=pathlib.Path(__file__).resolve().parent;batch=P.parents[1];project=P.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
context=[]
for f in [project/'AGENTS.md',project/'sources/upstream.json',project/'sources/CONTENTS.md',batch/'AGENTS.md',batch/'NEXT.md',batch/'ledger.json',batch/'prior-campaign-context.json']:
 row={'path':str(f),'sha256':sha(f)}
 if f.name in ['ledger.json','prior-campaign-context.json']:
  j=json.loads(f.read_text());row['accepted']=[{'number':x.get('number'),'title':x.get('title'),'scope':x.get('scope')} for x in j.get('accepted',[])];row['other_keys']=list(j)
  print(f.name,json.dumps(row['accepted'],ensure_ascii=False))
 context.append(row)
(P/'context-read.json').write_text(json.dumps(context,indent=2))
reg=[]
for name in ['omega-delta.json','omega-from-full-baseline.json']:
 f=P/'sources'/name
 if f.exists():
  d=json.loads(f.read_text());paths=[x['filename'] for x in d.get('files',[])];reg.append({'name':name,'sha256':sha(f),'status':d.get('status'),'total_commits':d.get('total_commits'),'commits_returned':len(d.get('commits',[])),'files_returned':len(paths),'paths':paths,'specific_name_hits':[x for x in paths if re.search('eruguz|benford|hyman|customer|fragmentation',x,re.I)],'limit':'Compare file cap300; no semantic absence or complete-current-tree claim.'})
(P/'live-compare-inspection.json').write_text(json.dumps(reg,indent=2))
obj={'lane':P.name,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'counts_unchanged':{'additional':8,'total':38},'source_dispositions':{'eruguz':'EXCLUDE_ROUTINE','hyman':'SOURCE_SCOPE_HOLD','box_fragmentation':'UNRESOLVED_PUBLIC_CLOSEST_BODY_HOLD'},'http':json.loads((P/'http.json').read_text()),'heads':json.loads((P/'heads.json').read_text()),'registry_limits':'Cached complete dated path trees plus live head and bounded raw compare. Selected current body read, not all-body audit; no worldwide or current semantic absence certificate. Older exploratory tree superseded by final-freeze baseline.','access_limits':'All lane HTTP requests200. No retries/bypass. ArXiv versioned originals/successor and actual institutional VoR identified. No subscription index search or corrected successor journal comparison.','exact_gap':'No eligible substantive full ordinary result. Retail linear model reduced to routine calculus; persistence N quantifier missing; full all-law fragmentation maximum criterion not proved.','strongest_objection':'Retail proof may be unprinted; this does not overcome explicit exclusion of routine derivatives. Fragmentation successor may intend centered logs; no claim that intended theorem is false.','falsifiers':'Obtain an exact wider nonlinear-demand source conjecture and substantive mechanism; obtain explicit persistence N convention; obtain corrected successor or full original fragmentation proof.','validation':json.loads((P/'checks.json').read_text()),'resource_guard':{'sha256':sha(P/'helper_guard.py'),'copied_from':'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'nominal_poll_seconds':0.04,'BLAS_threads':1,'caps_raised':False},'prohibited_actions':{'children':False,'git':False,'browser':False,'account':False,'contact':False,'post':False,'upload':False,'shared_writes':False},'files':[]}
for f in sorted(P.rglob('*')):
 if f.is_file() and f.name!='provenance.json':obj['files'].append({'path':str(f.relative_to(P)),'bytes':f.stat().st_size,'sha256':sha(f)})
(P/'provenance.json').write_text(json.dumps(obj,indent=2));print('manifest files',len(obj['files']))

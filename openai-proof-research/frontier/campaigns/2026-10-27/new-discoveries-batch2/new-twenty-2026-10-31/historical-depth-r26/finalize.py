import pathlib,json,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30));os.sched_setaffinity(0,{0,1})
D=pathlib.Path(__file__).resolve().parent;C=D.parent;B=C.parent;H=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'reservation.json').read_text());raw=json.loads((D/'raw-bindings.json').read_text());old=json.loads((D/'inherited-exact-entries.json').read_text())
res={}
for id,x in old.items():
 statement=raw[id]['record']['statement'];assert statement==x.get('statement',x.get('literal_statement'))
 sh=H(statement.encode());assert sh==x.get('statement_sha256',x.get('literal_sha256'))
 res[id]=dict(mathdb_id=int(id),old_disposition=x['disposition'],old_report=r['prior_coverage'][id]['report'],inherited=x,raw={k:v for k,v in raw[id].items() if k!='record'},literal_statement=statement,literal_statement_sha256=sh,new_outcome='RETAIN_INHERITED_HOLD_OR_PARK',new_primary_body_review=False,new_proof_body_review=False,new_record_coverage_credit=0,accepted_credit=0,full_scope_proof=False,Lean_endpoint=False,source_scope_cleared=False,novelty_cleared=False,remaining_lemma_or_gap=x.get('reason',x.get('concrete_reason',x.get('individual_reason'))),new_notes='No new primary-body evidence for this ID. Existing objections retained. Routing reviewed:false is stale.',sources=[])
updates={
'384372':('HOLD_EXPLICIT_MEASURE_AND_SIMPLE_PROOF_GAP',['BMV2004','Stahl'],'DEPTH.md Rank1: signed-cycle obstruction, conditional hypergeometric regrouping and known contour formula; no universal new positivity identity.'),
'384601':('PARK_PUBLIC_BOUNDARY_CONSTANT_HALF_FULL_SCOPE_UNRESOLVED',['HH2018','Larson','HH2026'],'DEPTH.md Rank2: public sharp boundary-mean constants do not settle volume-power constants; original workshop context still not directly recovered.'),
'384725':('EXCLUDE_NEW_CREDIT_DIRECT_PUBLIC_FULL_LINEAR_BOUND',['Cross2026'],'DEPTH.md Rank3: Gehrunger Theorem1.1 and Sections2–5 prove the direct universal linear crossing bound; reported external Lean not replayed.')}
for id,(out,ss,note) in updates.items():
 res[id].update(new_outcome=out,new_primary_body_review=True,new_proof_body_review=True,new_notes=note,remaining_lemma_or_gap=note,sources=[json.loads((D/'sources'/f'{s}.receipt.json').read_text()) for s in ss])
res['384506'].update(new_outcome='HOLD_PRIMARY_GAP_RECONFIRMED',new_notes='Primary definitions not recovered; original objection retained. No mathematical scope fixed by inference from the title.')
assert len(res)==40 and set(res)==set(map(str,r['ids']));(D/'results.json').write_text(json.dumps(res,indent=2))
# Reuse complete preprint subtree by content hash, never confuse truncated root cache with completeness.
p=C/'fresh-corpus-r5/openai-preprints.body';data=p.read_bytes();tree=json.loads(data);assert H(data)=='6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305';assert tree['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec' and tree['truncated']==False
head=json.loads((D/'sources/openai-head').read_text())['sha'];assert head=='4eaee87548250b2682affda7d05d947c05554bae'
hits=[x['path'] for x in tree['tree'] if any(w in x['path'].lower() for w in ['bmv','hermite-hadamard','crossing-famil','exponential-results'])]
(D/'registry-review.json').write_text(json.dumps(dict(head=head,live_head_receipt='sources/openai-head.receipt.json',complete_preprints_tree_sha=tree['sha'],reused_path=str(p.resolve()),reused_sha256=H(data),hits=hits,scope='Bounded path-name screen only; no full-registry body audit, no absence-as-novelty clearance. Root cache truncated. Direct live arXiv crossing-family and author HH proof bodies separately inspected.'),indent=2))
# Bind context without copying historical trees.
context=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',C/'ledger.json',pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json')]:
 if p.exists():context.append(dict(path=str(p.resolve()),sha256=H(p.read_bytes()),mutable=p==C/'ledger.json'))
(D/'context-bindings.json').write_text(json.dumps(context,indent=2))
print('40 exact literal hashes match inherited reports; complete cached preprint subtree verified; current HEAD unchanged.')

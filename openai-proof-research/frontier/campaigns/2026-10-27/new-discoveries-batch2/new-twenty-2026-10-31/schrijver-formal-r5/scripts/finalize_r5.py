from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent.parent
fresh=r/'fresh-extraction-r5'
replay=json.loads((fresh/'replay-result.json').read_text())
assert replay['status']=='PASS_UNCONDITIONAL'
order=json.loads((r/'outputs/modules.json').read_text())
assert len(replay['runs'])==2*len(order)
assert all(t.get('exit',0)==0 for t in replay['runs'])
assert len(replay['negative'])==7
frozen=json.loads((r/'frozen-before.json').read_text())
assert frozen==json.loads((r/'frozen-after.json').read_text())
assert all(hashlib.sha256((r/'src'/n).read_bytes()).hexdigest()==h for n,h in frozen.items())
audits={}
for name in ['ClosureAuditRound5','AuditRound5']:
 runs=[t for t in replay['runs'] if t['name']=='build-'+name];assert len(runs)==1
 p=fresh/runs[0]['log'];s=p.read_text()
 total=int(re.findall(r'TOTAL_LOCAL_DECLARATIONS (\d+)',s)[-1])
 mods=re.findall(r'^AUDIT_MODULE (\w+)',s,re.M)
 if name=='ClosureAuditRound5':assert set(mods)==set(json.loads((r/'outputs/endpoint-closure-r5.json').read_text()))
 assert all(x=='false' for x in re.findall(r'^(?:UNSAFE|PARTIAL|EXTERN) (\w+)',s,re.M))
 assert all(x=='none' for x in re.findall(r'^IMPLEMENTED_BY (\w+)',s,re.M))
 audits[name]=dict(modules=len(mods),declarations=total,log=str(p.relative_to(r)),log_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),passed=True)
endpointlog=next(t['log'] for t in replay['runs'] if t['name']=='build-EndpointRound5')
endpointtext=(fresh/endpointlog).read_text()
assert 'Schrijver.mathdb_352827' in endpointtext and 'sorryAx' not in endpointtext
result=dict(lane='schrijver-formal-r5',status='FORMAL_ENDPOINT_PROVED_VALIDATED_ROOT_REVIEW_REQUIRED',self_accepted=False,accepted_credit=0,root_decides=True,
 endpoint='Schrijver.mathdb_352827 : ¬ SchrijverUnitGap',endpoint_file='src/EndpointRound5.lean',remaining_Props=[],enumerations_proved=['Enumeration27','Enumeration28'],
 lean='4.34.1',mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',allowed_axioms=['propext','Classical.choice','Quot.sound'],endpoint_axioms_output=endpointtext.strip(),
 frozen=dict(modules=len(frozen),byte_identical=True,round4_archive_sha256='79d7782df41e7e9a52c67b34eaa60ef0fa76b66d6b3e645a8942a70747f83e57',before='frozen-before.json',after='frozen-after.json'),
 modules={m:dict(sha256=hashlib.sha256((r/'src'/f'{m}.lean').read_bytes()).hexdigest(),frozen=f'{m}.lean' in frozen) for m in order},
 audits=audits,replay=dict(status=replay['status'],modules=len(order),strict_builds=len(order),leanchecker_passes=len(order),negative_controls=replay['negative'],runs=len(replay['runs']),wall_seconds=sum(t.get('wall_seconds',0) for t in replay['runs']),max_process_seconds=max(t.get('wall_seconds',0) for t in replay['runs']),peak_private_bytes=max(t.get('peak_private_bytes',0) for t in replay['runs']),cap_failures=[t for t in replay['runs'] if t.get('cap_reason')],receipt='fresh-extraction-r5/replay-result.json'),
 source_zip=dict(path='schrijver-source-r5.zip',sha256=hashlib.sha256((r/'schrijver-source-r5.zip').read_bytes()).hexdigest()),
 limitations=['Journal DAM 350 (2024) body unread, per root ruling','No new novelty clearance; no acceptance claimed'],
 development_exceptions=['Failed initial full-validity comparison exceeded Lean -M3500 memory threshold; final comparisons use only cyclic endpoint filter','Initial audit caught compiler-generated partial companion; final noncomputable generator passes audits'],prohibited_actions=dict(child_agents=False,git=False,shared_ledger_edits=False,uploads=False,external_messages=False,browser_tabs=False,network_requests=False))
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','endpoint','remaining_Props','audits','replay']},indent=2))

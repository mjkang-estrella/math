from pathlib import Path
import json,hashlib,re,datetime
r=Path(__file__).resolve().parent;p=r.parent
h=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
def write(name,v):(r/name).write_text(json.dumps(v,indent=2)+'\n')
manifest=json.loads((r/'SOURCE-MANIFEST.json').read_text());assert all(h(r/n)==v and h(r/'fresh-replay'/n)==v for n,v in manifest.items())
before=json.loads((r/'input-hashes-before.json').read_text());after={x:h(p/x) for x in before};assert before==after
write('input-hashes-after.json',after)
expected={'edgepattern-formal-r5/edgepattern-r5-source.zip':'59c06fd1339a8d3beced9b8d6ce022d2d2e65d308c9aa1299db3e858f531dcc6','edgepattern-formal-r5/auditor-final-source.zip':'84ee704b498b5769d047517397fceae86c829206f633587d961d518341d640c6','expanded-corpus-r103/EDGE-PROOF.md':'1ae6f03f83828a33061ccb1b062db4347a682f0b3fbf3cb6113d00fc3b7009a0'}
assert all(before[x]==y for x,y in expected.items())
formal={x.name:h(x) for x in (r/'formal').glob('*.lean')};assert len(formal)==274
assert all(h(p/'edgepattern-formal-r5/formal'/n)==v for n,v in formal.items())
assert all(h(r/'fresh-replay/formal'/n)==v for n,v in formal.items())
modules=json.loads((r/'scripts/modules.json').read_text());assert len(modules)==269
closure=set()
def visit(n):
 if n in closure:return
 closure.add(n)
 for line in (r/'formal'/f'{n}.lean').read_text().splitlines():
  if line.startswith('import '):
   for k in line.split()[1:]:
    if (r/'formal'/f'{k}.lean').exists():visit(k)
visit('EndpointR5');assert len(closure)==268 and not any(x.startswith('Audit') for x in closure)
assert set(modules)==closure|{'AuditR5'}
# Source token screen is corroborative; the kernel audit is decisive.
banned=[]
for n in sorted(closure):
 txt=(r/'formal'/f'{n}.lean').read_text()
 for pat in [r'\bsorry\b',r'\badmit\b',r'^\s*axiom\b',r'^\s*unsafe\b',r'\bnative_decide\b',r'\bofReduceBool\b']:
  if re.search(pat,txt,re.M):banned.append([n,pat])
assert not banned
write('receipts/bindings.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_bound_inputs_unchanged':True,'count':len(before),'required_hashes':expected,'formal_byte_identity':True,'formal_files':len(formal),'proof_closure_modules':len(closure),'build_modules':len(modules),'proof_closure_excludes_auditors':True,'lexical_findings':banned})
replay=json.loads((r/'fresh-replay/replay-receipt.json').read_text());assert replay['passed'] and len(replay['checks'])==539
neg=json.loads((r/'fresh-replay/negative-results.json').read_text());assert neg['passed'] and len(neg['checks'])==6
safety=json.loads((r/'fresh-replay/auditor-safety-receipt.json').read_text());assert safety['passed']
assert 'PASS: strict rebuild' in (r/'receipts/replay-driver.log').read_text()
resources=[json.loads(q.read_text()) for q in (r/'fresh-replay/logs').glob('*.receipt.json')]
assert all(q['killed'] is None and q['elapsed_seconds']<140 and q['peak_sampled_private_rss_bytes']<=6*1024**3 for q in resources)
assert all(q['cpu_limit_seconds']==120 and q['wall_limit_seconds']==140 for q in resources)
assert all(len(q['command'])==2 for q in resources if Path(q['command'][0]).name=='leanchecker')
write('receipts/replay-summary.json',{'passed':True,'strict_compilations':269,'one_module_kernel_checks':269,'guarded_calls':len(resources),'negative_checks':neg,'auditor_safety':safety,'peak_sampled_private_rss_bytes':max(q['peak_sampled_private_rss_bytes'] for q in resources),'longest_guarded_call_seconds':max(q['elapsed_seconds'] for q in resources),'resource_kills':0,'final_pass_line':(r/'receipts/replay-driver.log').read_text().splitlines()[-1]})
print('PASS: bindings, 274 identical sources, 268-module proof closure, replay and resource receipts')

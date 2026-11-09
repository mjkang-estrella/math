from pathlib import Path
import json,hashlib,re,datetime
b=Path(__file__).resolve().parent;f=b/'fresh';log=(f/'logs/replay-AuditR5.log').read_text()
blocks=re.findall(r'DECL ([^\n]+)\nMODULE ([^\n]+)\nUNSAFE ([^\n]+)\nPARTIAL ([^\n]+)\nTYPE_NODE (\d+)\nBODY ([^\n]+)\nAXIOMS ([^\n]+)',log)
assert blocks
nodes={int(i):row for i,row in re.findall(r'EXPR_NODE (\d+) ([^\n]+)',log)}
assert set(nodes)==set(range(len(nodes)))
assert not any(row.startswith(('fvar ','mvar ')) for row in nodes.values())
for x in blocks:
 assert int(x[4]) in nodes
 if x[5].startswith('node '):assert int(x[5][5:]) in nodes
assert 'TOTAL_POLICY_VIOLATIONS 0' in log and 'FUEL_EXHAUSTED' not in log
assert len(blocks)==int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',log).group(1))
mods=set(json.loads((b/'closure-independent.json').read_text())['proof_modules']);seen={x[1] for x in blocks}
assert mods<=seen,(mods-seen)
for name,mod,unsafe,partial,ty,body,axioms in blocks:
 assert unsafe=='false' and partial=='false',(name,unsafe,partial)
 axs=set(x.strip() for x in axioms.strip('[]').split(',') if x.strip())
 assert axs<={'propext','Classical.choice','Quot.sound'},(name,axs)
replay=json.loads((f/'replay-receipt.json').read_text());assert replay['passed']
negative=json.loads((f/'negative-results.json').read_text());assert negative['passed']
safety=json.loads((f/'auditor-safety-receipt.json').read_text());assert safety['passed']
rs=[json.loads(x.read_text()) for x in (f/'logs').glob('*.log.receipt.json')]
assert all(not r['killed'] for r in rs)
assert max(r['peak_sampled_private_rss_bytes'] for r in rs)<6*1024**3
before=json.loads((b/'inputs-before.json').read_text());after={p:hashlib.sha256((b.parent/p).read_bytes()).hexdigest() for p in before}
(b/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n');assert before==after
# All extracted formal source bytes must still equal the ones the replay recorded.
assert all(hashlib.sha256((f/p).read_bytes()).hexdigest()==sha for p,sha in replay['formal_source_sha256'].items())
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'proof_modules':len(mods),'compiled_modules':sum(x['name'].startswith('replay-') for x in replay['checks']),'leanchecker_modules':sum(x['name'].startswith('leanchecker-') for x in replay['checks']),'audited_local_declarations':len(blocks),'audited_modules':sorted(seen),'expression_nodes':int(re.search(r'TOTAL_EXPR_NODES (\d+)',log).group(1)),'negative_controls':negative,'auditor_safety':safety,'max_sampled_private_rss_bytes':max(r['peak_sampled_private_rss_bytes'] for r in rs),'max_wall_seconds':max(r['elapsed_seconds'] for r in rs),'unchanged_bound_inputs':len(before),'available_bodies_audited':True,'declarations_without_value':[x[0] for x in blocks if x[5]=='none'],'forbidden_axioms':[],'unsafe_or_partial':[]}
(b/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

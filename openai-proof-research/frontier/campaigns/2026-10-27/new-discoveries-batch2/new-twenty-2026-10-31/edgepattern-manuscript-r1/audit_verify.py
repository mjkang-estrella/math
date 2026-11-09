from pathlib import Path
import json,re
r=Path(__file__).resolve().parent;log=(r/'fresh-replay/logs/replay-AuditR5.log').read_text()
blocks=re.findall(r'DECL ([^\n]+)\nMODULE ([^\n]+)\nUNSAFE ([^\n]+)\nPARTIAL ([^\n]+)\nTYPE_NODE (\d+)\nBODY ([^\n]+)\nAXIOMS ([^\n]+)',log)
nodes={int(i):row for i,row in re.findall(r'EXPR_NODE (\d+) ([^\n]+)',log)}
assert blocks and set(nodes)==set(range(len(nodes)))
assert not any(row.startswith(('fvar ','mvar ')) for row in nodes.values())
assert 'TOTAL_POLICY_VIOLATIONS 0' in log and 'FUEL_EXHAUSTED' not in log
assert len(blocks)==int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',log).group(1))
assert len(nodes)==int(re.search(r'TOTAL_EXPR_NODES (\d+)',log).group(1))
for name,mod,unsafe,partial,ty,body,axs in blocks:
 assert unsafe=='false' and partial=='false',(name,unsafe,partial)
 assert int(ty) in nodes
 if body.startswith('node '):assert int(body[5:]) in nodes
 assert {x.strip() for x in axs.strip('[]').split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
mods=set(json.loads((r/'scripts/modules.json').read_text()))-{'AuditR5'}
assert mods<={b[1] for b in blocks}
safety=(r/'fresh-replay/logs/auditor-safety.log').read_text()
assert 'error:' not in safety
(r/'receipts/audit-parse.json').write_text(json.dumps({'passed':True,'declarations':len(blocks),'expression_nodes':len(nodes),'proof_modules_covered':len(mods),'policy_violations':0,'unsafe_or_partial':[],'forbidden_axioms':[],'declarations_without_value':[b[0] for b in blocks if b[5]=='none'],'auditor_safety_log':safety},indent=2)+'\n')
print('PASS: full expression DAG, declaration coverage, safety and axioms')

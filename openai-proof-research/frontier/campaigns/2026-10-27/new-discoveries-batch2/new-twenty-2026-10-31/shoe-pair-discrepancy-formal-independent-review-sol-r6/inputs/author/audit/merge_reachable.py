from pathlib import Path
import json, subprocess, hashlib
p=Path('logs/1794121252684594732_lean_ShoeReachableAudit.log')
nodes={}; roots=None; endpoints=None; complete=None
for line in p.open():
    if line.startswith('AUDIT_ROOTS '): roots=json.loads(line[len('AUDIT_ROOTS '):])
    elif line.startswith('AUDIT_ENDPOINTS '): endpoints=json.loads(line[len('AUDIT_ENDPOINTS '):])
    elif line.startswith('AUDIT_NODE '):
        d=json.loads(line[len('AUDIT_NODE '):]); n=d['name']
        assert n not in nodes or nodes[n]==d
        nodes[n]=d
    elif line.startswith('AUDIT_COMPLETE '): complete=int(line.split()[1])
assert complete==len(nodes) and roots and endpoints
for d in nodes.values():
    assert all(n in nodes for n in d['typeDependencies']+d['bodyDependencies'])
def closure(roots):
    seen=set(); pending=list(roots)
    while pending:
        n=pending.pop()
        if n in seen: continue
        seen.add(n); d=nodes[n]
        pending.extend(d['typeDependencies']); pending.extend(d['bodyDependencies'])
    return sorted(seen)
assert set(closure(roots))==set(nodes)
reports={}
for n in endpoints:
    c=closure([n]); ax=[x for x in c if nodes[x]['isAxiom']]
    reports[n]={'closure':c,'count':len(c),'axioms':ax,'unsafe':[x for x in c if nodes[x]['unsafe']]}
origins={}
for d in nodes.values(): origins[d['origin']]=origins.get(d['origin'],0)+1
result={'complete':True,'scope':'All actual production-origin declarations including private/generated, and shared reachable type/body DAG; no unrelated environment dump','root_count':len(roots),'node_count':len(nodes),'origins':origins,'roots':roots,'endpoints':reports,'axioms':sorted(n for n,d in nodes.items() if d['isAxiom']),'unsafe':sorted(n for n,d in nodes.items() if d['unsafe']),'log_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tool_module':'ShoeReachableAudit (not imported by proofs)','not_final_transport_audit':True}
for name,data in [('audit/reachable-nodes.json',nodes),('audit/reachable-report.json',result)]:
    subprocess.run(['python3','-I','-B','write_lane.py',name],input=json.dumps(data,sort_keys=True),text=True,check=True)
print(json.dumps({k:v for k,v in result.items() if k not in ['roots','endpoints']},indent=2))
print(json.dumps({n:{k:v for k,v in d.items() if k!='closure'} for n,d in reports.items()},indent=2))

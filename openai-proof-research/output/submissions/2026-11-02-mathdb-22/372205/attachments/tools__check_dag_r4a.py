import json,sys,re
from pathlib import Path
nodes={};decls={}
for line in Path(sys.argv[1]).open():
 row=json.loads(line)
 if 'node' in row:
  idx=row['node'];value=(row['ctor'],row['fields'])
  if idx in nodes: assert nodes[idx]==value,('conflicting node',idx)
  nodes[idx]=value
 else:
  name=row['declaration'];assert name not in decls,('duplicate declaration',name)
  decls[name]=row
assert set(nodes)==set(range(len(nodes)))
refs={'app':[0,1],'lam':[1,2],'forallE':[1,2],'letE':[1,2,3],'mdata':[1],'proj':[2],'leaf':[]}
for idx,(tag,fields) in nodes.items():
 for i in refs[tag]: assert fields[i] in nodes,('missing child',idx,fields[i])
for name,row in decls.items():
 assert row['full_type_root'] in nodes
 assert row['full_body_value_true_root'] is None or row['full_body_value_true_root'] in nodes
log=Path('logs/AuditR4a.log').read_text()
assert len(decls)==int(re.search(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',log).group(1))
assert set(re.findall(r'DECL\|([^|\n]+)\|MODULE',log))==set(decls)
summary={'status':'pass','encoding':'lossless shared Expr DAG; all constructors, fields and child links; roots from c.type and c.value? true','nodes':len(nodes),'declarations':len(decls)}
Path('logs/audit-r4a-dag-check-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))

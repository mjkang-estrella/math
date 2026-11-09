import json,re
from pathlib import Path
mods=json.loads(Path('modules.json').read_text());groups=json.loads(Path('audit-groups.json').read_text())
pairs=[];counts={}
for a in groups:
 log=Path(f'logs/{a}.log').read_text()
 ds=re.findall(r'DECL\|([^|\n]+)\|MODULE\|([^|\n]+)\|UNSAFE\|false\|PARTIAL\|false\|AXIOMS\|([^\n]+)',log)
 assert len(ds)==int(re.search(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',log)[1])
 nodes={};decls={}
 for line in Path(f'logs/audit-all-{groups.index(a)}-dag.jsonl').open():
  row=json.loads(line)
  if 'node' in row:nodes[row['node']]=(row['ctor'],row['fields'])
  else:decls[row['declaration']]=row
 assert set(decls)==set(n for n,m,ax in ds)
 refs={'app':[0,1],'lam':[1,2],'forallE':[1,2],'letE':[1,2,3],'mdata':[1],'proj':[2],'leaf':[]}
 for idx,(tag,fields) in nodes.items():
  for i in refs[tag]:assert fields[i] in nodes
 for row in decls.values():
  assert row['full_type_root'] in nodes
  assert row['full_body_value_true_root'] is None or row['full_body_value_true_root'] in nodes
 for n,m,ax in ds:
  pairs.append((n,m));counts[m]=counts.get(m,0)+1
assert len(pairs)==len(set(n for n,m in pairs))
assert set(counts)=={m for m in mods if 'Audit' not in m}
Path('logs/full-audit-summary.json').write_text(json.dumps({'declarations':len(pairs),'by_module':counts,'status':'pass'},indent=2)+'\n')
print('FULL_AUDIT_PASS',len(pairs))

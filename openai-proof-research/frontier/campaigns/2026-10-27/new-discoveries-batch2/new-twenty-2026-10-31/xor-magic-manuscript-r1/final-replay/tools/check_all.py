import json,re,hashlib
from pathlib import Path
mods=json.loads(Path('modules.json').read_text());groups=json.loads(Path('audit-groups.json').read_text())
pairs=[];counts={};canonical={};duplicates=[]
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
 memo={}
 def digest(idx):
  if idx is None:return None
  if idx in memo:return memo[idx]
  tag,fields=nodes[idx];fields=fields.copy()
  for i in refs[tag]:fields[i]=digest(fields[i])
  memo[idx]=hashlib.sha256(json.dumps([tag,fields]).encode()).hexdigest()
  return memo[idx]
 for n,m,ax in ds:
  row=decls[n]
  hashes=(digest(row['full_type_root']),digest(row['full_body_value_true_root']))
  if n in canonical:
   assert canonical[n]['hashes']==hashes,('inconsistent duplicate',n)
   duplicates.append({'name':n,'modules':[canonical[n]['module'],m],'type_sha256':hashes[0],'body_sha256':hashes[1]})
  else:canonical[n]={'hashes':hashes,'module':m}
  pairs.append((n,m));counts[m]=counts.get(m,0)+1
assert len(pairs)==len(set(pairs))
assert set(counts)=={m for m in mods if 'Audit' not in m}
Path('logs/full-audit-summary.json').write_text(json.dumps({'declarations':len(canonical),'declaration_occurrences':len(pairs),'duplicate_generated_declarations':duplicates,'by_module':counts,'status':'pass'},indent=2)+'\n')
print('FULL_AUDIT_PASS',len(canonical),'unique;',len(pairs),'occurrences')

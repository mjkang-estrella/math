from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'source-bindings.json').read_text())
for r in json.loads((L/'frozen/hulls/source-bindings.json').read_text()):
 p=Path(r['original']);d=L/'frozen/exact'/r['copy']
 d.parent.mkdir(parents=True,exist_ok=True)
 assert sha(p)==r['sha256'];shutil.copyfile(p,d);assert sha(d)==sha(p)==r['sha256']
 records.append(dict(original=str(p),copy=str(d.relative_to(L)),sha256=sha(p)))
(L/'source-bindings.json').write_text(json.dumps(records,indent=2)+'\n')
for n in ['Literal','InstanceG','InstanceH','Rank','Hulls','Geometry']:
 shutil.copyfile(L/'frozen/hulls'/f'{n}.lean',L/f'{n}.lean')
for n in ['runner.py','pins.json']:shutil.copyfile(L/'frozen/hulls'/n,L/n)
support=(L/'frozen/hulls/AuditSupportRank.lean').read_text()
support=support.replace('[`Rank]','[`Literal, `InstanceG, `InstanceH, `Rank, `Hulls]')
support=support.replace('logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"','logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"\n       logInfo m!"OWN_PARTIAL {name} {info.isPartial}"\n       if info.isPartial then throwError m!"REJECTED partial declaration {name}"')
support=support.replace('if info.isUnsafe then throwError m!"Rejected transitive dependency {name}"','if info.isPartial then throwError m!"REJECTED partial transitive dependency {name}"\n       if info.isUnsafe then throwError m!"REJECTED unsafe transitive dependency {name}"')
(L/'AuditSupport.lean').write_text(support)
(L/'AuditInherited.lean').write_text('import Geometry\nimport InstanceG\nimport InstanceH\nimport AuditSupport\n#literal_inventory\n#audit_all\n')
print('prepared frozen direct exact sources and strict audit')

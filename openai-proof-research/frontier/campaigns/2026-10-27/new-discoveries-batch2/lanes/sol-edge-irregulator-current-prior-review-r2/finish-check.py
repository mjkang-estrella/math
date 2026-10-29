from pathlib import Path
import hashlib,json,datetime,re
P=Path(__file__).resolve().parent;F=json.loads((P/'context/review-freeze.json').read_text());S=Path(F['source_lane']);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks={k:{'source':sha(S/k)==v,'copy':sha(P/'candidate'/k)==v} for k,v in F['files'].items()}
members=lambda root:sorted(str(p.relative_to(root)) for p in root.rglob('*') if p.is_file())
a={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'source_membership_matches':members(S)==sorted(F['files']),'copy_membership_matches':members(P/'candidate')==sorted(F['files']),'all_hashes_pass':all(all(v.values()) for v in checks.values())}
(P/'freeze-after.json').write_text(json.dumps(a,indent=2));print({k:v for k,v in a.items() if k!='checks'})
# saved tree identities and exact copied bodies are tied to tree blob IDs using git's documented blob hash, without Git access
rows={}
for repo in ['omega','openai']:
 tree=P/'registry'/f'{repo}-tree.txt';n=0;paths={}
 with tree.open() as f:
  for line in f:
   n+=1;meta,path=line.rstrip().split('\t',1);paths[path]=meta.split()[2]
 bodychecks={}
 if repo=='omega':
  for p in (P/'registry/current-bodies').rglob('*'):
   if p.is_file():
    data=p.read_bytes();h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();rel=str(p.relative_to(P/'registry/current-bodies'));bodychecks[rel]={'tree_blob':paths[rel],'computed_blob':h,'match':paths[rel]==h}
 else:
  data=(P/'registry/openai-CONTENTS.md').read_bytes();h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();bodychecks['CONTENTS.md']={'tree_blob':paths['CONTENTS.md'],'computed_blob':h,'match':h==paths['CONTENTS.md']}
 rows[repo]={'lines':n,'sha256':sha(tree),'bodies':bodychecks}
(P/'tree-body-checks.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))

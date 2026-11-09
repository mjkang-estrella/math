from pathlib import Path
import json,hashlib,shutil,re
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');C=B/'frontier/campaigns/2026-10-14';O=C/'t088p133-manuscript-review-r1';P=O/'packet/public'
a=json.loads((O/'evidence/authentication-before.json').read_text());z=json.loads((O/'evidence/authentication-after.json').read_text());assert all(z[k]==v for k,v in a.items())
shutil.copy2(O/'evidence/authentication-after.json',P/'evidence/authentication-after.json');shutil.copy2(O/'work/authenticate.py',P/'code/authenticate.py')
if not (P/'renders').exists():shutil.copytree(O/'renders',P/'renders')
record=json.loads((P/'read-record.json').read_text());counts={'immutable_named_matches':0,'parent_live_observations_excluded':0}
for row in record['records']:
 if row['kind'] in ['live_observation','parent_observation']:counts['parent_live_observations_excluded']+=1;continue
 q=B/row['path'];st=q.lstat();assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256'] and st.st_size==row['bytes'] and (st.st_mode&0o777)==row['mode'] and st.st_nlink==row['nlink'],str(q)
 counts['immutable_named_matches']+=1
r1=(C/'t088p133-manuscript-r1/packet/public/references.tex').read_text();r2=(C/'t088p133-manuscript-r2/packet/public/references.tex').read_text();entries=lambda s:re.findall(r'\\bibitem\{.*?(?=\\bibitem|\\end\{thebibliography\})',s,re.S)
assert [v.strip() for v in entries(r1)]==[v.strip() for v in entries(r2)[:11]]
counts.update(seven_package_anchors_and_named_manifests_match=True,initial_six_authentication_records_identical=True,original_bibliography_entries_preserved=11,scope='Named immutable read files plus authenticated manifest scopes;not whole-parent/root scratch or OS tracing')
(P/'evidence/preservation.json').write_text(json.dumps(counts,indent=2)+'\n');print(json.dumps(counts))

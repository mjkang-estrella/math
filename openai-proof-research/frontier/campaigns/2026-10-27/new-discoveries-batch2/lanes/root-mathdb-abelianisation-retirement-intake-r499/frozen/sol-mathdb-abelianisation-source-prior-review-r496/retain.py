from pathlib import Path
import hashlib,json,shutil
D=Path(__file__).resolve().parent; L=D.parent; R=L/'root-mathdb-three-candidate-intake-r493'; A=R/'frozen/claude-mathdb-primary-qualified-breadth-r480'
def bind(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
checks=[]
for r in [R,A]:
 m=json.loads((r/'manifest.json').read_text()); expected={x['path'] for x in m['files']}; excluded=set(m.get('excluded_exact_paths',m.get('excluded_exact',[])));actual={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file()}
 assert actual-excluded==expected,(str(r),sorted(actual-excluded-expected),sorted(expected-actual))
 checks.append({'root':str(r),'exact_manifest_entries':len(expected),'excluded_exact_paths':sorted(excluded)})
bs=json.loads((R/'bindings.json').read_text()); direct=[]
for e in bs:
 for k in ['original','copy']:
  b=bind(Path(e[k])); assert b['sha256']==e['sha256'] and b['size']==e['size'],e[k]
 direct.append(e)
(D/'direct-intake-bindings-validated.json').write_text(json.dumps({'checks':checks,'direct_pairs_validated':len(direct),'bindings_source':bind(R/'bindings.json'),'method':'Every direct original and copy read and hashed; no upstream verifier; no recursive binding traversal or copies.'},indent=2)+'\n')
flat=[]
for src,name in [(A/'briefs/P2-339564-abelianisation-proof.md','author-P2-339564.md'),(A/'sources/arxiv/1806.06821.pdf','primary-1806.06821v2.pdf'),(A/'sources/arxiv/1806.06821.txt','primary-1806.06821v2.txt')]:
 shutil.copyfile(src,D/name);flat.append({'original':bind(L/'claude-mathdb-primary-qualified-breadth-r480'/src.relative_to(A)),'intake_copy':bind(src),'retained':bind(D/name)})
(D/'flat-original-bindings.json').write_text(json.dumps(flat,indent=2)+'\n')
metadata=next(x for x in json.loads((A/'retained-sources.json').read_text()) if x['arxiv']=='1806.06821')
(D/'source-provenance.json').write_text(json.dumps({'primary_upstream_metadata':metadata,'primary_retained_pdf':bind(D/'primary-1806.06821v2.pdf'),'primary_retained_text':bind(D/'primary-1806.06821v2.txt'),'successor':{'url':'https://aaltodoc.aalto.fi/server/api/core/bitstreams/ed28db5e-579f-4908-8055-24d45cd021df/content','http_status':200,'retrieved_utc':'2026-10-31T12:30:08Z','version':'Publisher PDF / version of record; LAA 708 (2025) 372-404; DOI 10.1016/j.laa.2024.12.003','publication_dates':'Body: received 16 Aug 2024; revised 22 Nov 2024; accepted 5 Dec 2024; available online 16 Dec 2024. Repository cover: 01/03/2025. Distinct date fields, no inferred v1 equivalence.','pdf':bind(D/'successor-published.pdf'),'text':bind(D/'successor-published.txt'),'binding_sequence':'PDF sha256+size recorded before pdftotext; derivative sha256+size recorded before rg/sed; source statement pages397,401 visually checked.'}},indent=2)+'\n')
print('Exact intake manifests and',len(direct),'direct original/copy pairs PASS; flat assigned sources retained.')

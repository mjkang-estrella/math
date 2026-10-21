from pathlib import Path
import json,hashlib,shutil
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); A=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r138'; R=P/'frontier/campaigns/2026-10-14/h138-proof-r1'
sha=lambda b:hashlib.sha256(b).hexdigest()
env={'FINAL.json':'a68c6359d92b71b9758765b5a1bc8bb5d160e5969e4498dd1f15ad0cb73d5a85','MANIFEST.json':'6fd9009523d53e032fa1e7ad77421cb26a36f8f618a1106c29cc447da66dee50','REPORT.md':'55182bd2a37581e2ada1938db32d51a279d9f59940e805b5d97728c4fe4889e2'}
for n,h in env.items(): assert sha((A/n).read_bytes())==h
m=json.loads((A/'MANIFEST.json').read_text()); sl=json.loads((A/'source-ledger.json').read_text()); pl=json.loads((A/'primary-ledger.json').read_text())
allow=['H-SCOPE.md','AUTHOR-PROOF.md','DERIVATION.md','freeze-receipt.json','REPORT.md','FINAL.json','READING-LIMITS.md','NOTES.md','README.md','source-ledger.json','primary-ledger.json','original-ledger.json','verify.py','MANIFEST.json']
allow += [x['local_path'] for x in sl]
for x in pl: allow += [x['local_path']]+[e['path'] for e in x['extracts']]
records=[]
for n in allow:
 b=(A/n).read_bytes()
 if n not in env: assert m['files'][n]=={'size':len(b),'sha256':sha(b)},n
 out=R/'private/incoming'/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
 records.append({'origin':str(A/n),'copy':str(out.relative_to(R)),'size':len(b),'sha256':sha(b)})
tree=(P/'sources/preprints-tree.json').read_bytes();assert sha(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
(R/'private/preprints-tree.json').write_bytes(tree)
t=json.loads(tree); nodes=t['tree'];assert len(nodes)==13223
by={x['path']:x for x in nodes}
for x in sl:
 b=(A/x['local_path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();cp=x['canonical_path']; key=cp.removeprefix('preprints/')
 node=by.get(cp,by.get(key));assert node and node['sha']==blob and node['size']==len(b),(cp,node)
for n in ['AGENTS.md','sources/upstream.json','frontier/iterations/i130-spectral-harmonic-discovery.md','frontier/iterations/i133-fixed-metric-harmonic-growth.md','frontier/iterations/iteration133-fixed-metric-harmonic-growth-task.json','frontier/iterations/iteration136-birational-positivity-discovery-task.json','frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/report.md']:
 b=(P/n).read_bytes();out=R/'private/originals'/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b);records.append({'origin':str(P/n),'copy':str(out.relative_to(R)),'size':len(b),'sha256':sha(b)})
(R/'incoming-membership.json').write_text(json.dumps({'anchors':env,'members':records,'original_root_authentication':'Detached envelopes and explicit selected payload bytes only; not whole original-root inventory. Original verifier not executed because its traversal lacks current exclusions. Reduced copy has own explicit membership, not original nested-manifest certification.','tree_count':len(nodes),'pinned_source_bindings':len(sl)},indent=2)+'\n')
print('Authenticated envelopes,',len(records),'selected incoming/current originals,',len(sl),'canonical source blobs, tree',len(nodes))

"""Capture bounded read-only input observations; writes only under this script's root."""
from pathlib import Path
import json,hashlib,io,gzip,tarfile,re,datetime
R=Path(__file__).resolve().parent;P=R.parents[3];A=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r138'
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(p):
 b=p.read_bytes();return {'size':len(b),'sha256':sha(b),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
entries=json.loads((R/'input-membership.json').read_text()); entries=list({e['original']:e for e in entries}.values())
for n in ['assessment.md','intake.json','replay.json']:
 src=P/'frontier/campaigns/2026-10-14/discovery-analytic-r138-parent'/n;dst=R/'private/parent'/n;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());entries.append(dict(original=str(src.relative_to(P)),copy=str(dst.relative_to(R)),**rec(src)))
src=P/'frontier/iterations/i136-birational-positivity-discovery.md';dst=R/'private/originals/frontier/iterations'/src.name;dst.write_bytes(src.read_bytes());entries.append(dict(original=str(src.relative_to(P)),copy=str(dst.relative_to(R)),**rec(src)))
entries=list({e['original']:e for e in entries}.values());dump(R/'input-membership.json',entries)
tree=json.loads((R/'private/originals/sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and not tree['truncated']; assert rec(R/'private/originals/sources/preprints-tree.json')['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
lookup={x['path']:x for x in tree['tree']}
source=[]
for e in json.loads((R/'private/incoming/source-ledger.json').read_text()):
 q=R/'private/source'/e['canonical_path']
 if not q.is_file():continue
 r=rec(q); t=lookup[e['canonical_path']];assert r['size']==e['size']==t['size'] and r['git_blob_sha1']==e['git_blob']==t['sha'] and r['sha256']==e['sha256']
 source.append(dict(canonical_path=e['canonical_path'],url=e['url'],copy=str(q.relative_to(R)),**r,lines=len(q.read_bytes().splitlines())))
dump(R/'source-authentication.json',{'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_entries':13223,'tree_sha256':rec(R/'private/originals/sources/preprints-tree.json')['sha256'],'files':source,'limits':'Canonical tree authentication, not source truth audit or semantic-read certificate.'})
primary=[]
for e in json.loads((R/'private/incoming/primary-ledger.json').read_text()):
 q=R/'private/primary'/e['id']/'raw.bin';b=q.read_bytes();assert sha(b)==e['sha256'] and len(b)==e['size']; extracts=[]
 try:
  with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tf:
   names={x.name.removeprefix('./'):x for x in tf.getmembers() if x.isfile()}
   for x in e['extracts']:
    rel=Path(x['path']).relative_to('private/primary/'+e['id']).as_posix();member=names.get(rel) or names.get(rel.removeprefix('text/'));v=tf.extractfile(member).read();p=R/'private/primary'/e['id']/rel;assert p.read_bytes()==v and sha(v)==x['sha256'];extracts.append(dict(path=str(p.relative_to(R)),**rec(p),lines=len(v.splitlines()),raw_member=member.name))
 except tarfile.ReadError:
  assert len(e['extracts'])==1;v=gzip.decompress(b);x=e['extracts'][0];p=R/x['path'];assert p.read_bytes()==v and sha(v)==x['sha256'];extracts.append(dict(path=str(p.relative_to(R)),**rec(p),lines=len(v.splitlines()),raw_member='single-file gzip'))
 primary.append({'id':e['id'],'url':e['url'],'raw':str(q.relative_to(R)),**rec(q),'extracts':extracts})
dump(R/'primary-authentication.json',{'versions':primary,'limits':'Versioned URLs and retained raw bindings; decompressed/extracted bytes independently compared without altering originals. No new current-version inference.'})
anchors={'FINAL.json':'a68c6359d92b71b9758765b5a1bc8bb5d160e5969e4498dd1f15ad0cb73d5a85','MANIFEST.json':'6fd9009523d53e032fa1e7ad77421cb26a36f8f618a1106c29cc447da66dee50','REPORT.md':'55182bd2a37581e2ada1938db32d51a279d9f59940e805b5d97728c4fe4889e2'}
for n,h in anchors.items():assert rec(A/n)['sha256']==h
m=json.loads((A/'MANIFEST.json').read_text());f=json.loads((A/'FINAL.json').read_text());assert f['manifest_sha256']==anchors['MANIFEST.json'] and f['report_sha256']==anchors['REPORT.md']
# Direct manifest-selected authentication. Excluded history/peer/copy roles are never opened.
skip=re.compile(r'private/control-fixture/|private/history-search|(?:^|/)discovery-analytic-r137-parent/|(?:^|/)fresh-analytic-discovery-r137/|h138[-_]|t185r144|structural.*r144|arithmetic.*r10[89]|arithmetic.*r110',re.I)
auth=[];omitted=[]
for n,e in m['files'].items():
 if skip.search(n):omitted.append(n);continue
 q=A/n;r=rec(q);assert r['size']==e['size'] and r['sha256']==e['sha256'];auth.append({'path':n,**r})
dump(R/'incoming-authentication.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root':str(A.relative_to(P)),'external_anchors':anchors,'envelopes_verified':True,'original_root_manifest_selected_authentication':auth,'excluded_unopened':omitted,'whole_root_certified':False,'reduced_copy_certified_by_original_manifest':False,'limits':'Actual original-root envelopes and permitted manifest-selected payload bytes checked separately from selective copies. Forbidden history/copied controls excluded before body selection. No original whole-root verifier execution or complete-root seal claim.'})
checks=[]
for e in entries:
 src=P/e['original'];dst=R/e['copy'];r=rec(src);assert r['sha256']==e['sha256']==rec(dst)['sha256'];checks.append({'original':e['original'],'copy':e['copy'],'sha256':e['sha256'],'current_matches_snapshot':True})
dump(R/'initial-input-observations.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selected_inputs':checks,'limits':'Current selected-original bytes only. Snapshots are after some direct readings, not first-read, whole-parent, historical or OS-preservation evidence.'})
print(json.dumps({'sources_authenticated':len(source),'primary_raw_versions':len(primary),'input_copies':len(entries),'author_allowed_payloads_authenticated':len(auth),'author_payloads_excluded':len(omitted)}))

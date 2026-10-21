#!/usr/bin/env python3
"""Authenticate Analytic157 and the explicitly disclosed mutable-parent drift."""
import datetime,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r157'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'a59f8e257f5081762c9b9ac545039b2d346b98ced46f27c1d02205cd81515b90','MANIFEST.json':'8fa7ba163e552b289b1d0458015abd3cbeaebe376b2cbd9080d3c5364533a9e5','REPORT.md':'b36f8fd6a48c395e5be811d2d935a61a90a55fdb5f4c46b5f8cb0358736548c8'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==550
 before=snap(ROOT);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==68 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-auth.json');assert len(source)==20
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable={};later=read(ROOT/'private/required-original-later-identities.json');initial=read(ROOT/'private/required-original-identities.json');assert len(later)==len(initial)==10
 changed=[]
 for e,f in zip(initial,later):
  q=P/e['path'];assert f['path']==e['path'] and f['initial']=={'size':e['size'],'sha256':e['sha256']} and q.stat().st_size==f['observed_later']['size'] and sha(q)==f['observed_later']['sha256']
  if f['unchanged']:assert sha(q)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':e['size'],'sha256':e['sha256']}
  else:
   assert e['path']=='frontier/campaigns/2026-10-14/discovery-analytic-r156-parent/assessment.md' and e['size']==5566 and q.stat().st_size==5828;assert hashlib.sha256(q.read_bytes()[:e['size']]).hexdigest()==e['sha256'];suffix=q.read_bytes()[e['size']:];assert len(suffix)==262 and suffix.startswith(b'\nArithmetic128 subsequently completed after the Analytic157 dispatch;');changed.append({'path':e['path'],'initial':f['initial'],'observed_current':f['observed_later'],'initial_prefix_exact':True,'append_bytes':262,'cause':'Parent appended Arithmetic128 terminal status after child initial read; no mathematical note/source bytes changed.','child_semantic_reread':False})
 assert len(stable)==9 and len(changed)==1
 history=read(ROOT/'private/history-identities.json');assert len(history)==9
 for e in history:
  p=P/e['original_path'];q=ROOT/e['selected_path'];a,b=e['lines'];assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256'] and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b]);stable[e['original_path']]={'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']}
 assert len(stable)==14 and (ROOT/'private/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 e=read(ROOT/'private/primary/younsi-auth.json');q=ROOT/'private/primary/1511.07348v1.incoming';assert q.stat().st_size==e['incoming_size'] and sha(q)==e['incoming_sha256']
 with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as tar:
  for s in e['selected']:
   p=q.parent/s['copy'];assert p.stat().st_size==s['size'] and sha(p)==s['sha256'] and tar.extractfile(s['member']).read()==p.read_bytes()
 e=read(ROOT/'private/primary/ahlfors-bers-auth.json');q=ROOT/'private/primary/ahlfors-bers-1960.pdf';assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(q.with_suffix('.txt'))==e['extract_sha256'];assert len(list(q.parent.glob('ab-page-*.png')))==3
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected';assert len(ctl['cases'])==7 and all(e['expected_accept']==e['actual_accept'] for e in ctl['cases']) and ctl['originals_unchanged']
 for e in read(ROOT/'private/controls/original-selection-identities.json'):
  p=ROOT/e['original'];q=fixture/e['selected'];assert p.stat().st_size==q.stat().st_size==e['original_size']==e['selected_size'] and sha(p)==sha(q)==e['original_sha256']==e['selected_sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic157-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);state0=snap(copy);args=[str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
  check('unchanged',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'CONTROL');check('changed_member',False);q.unlink();check('missing_member',False);q.write_bytes(data);q.chmod(state0[str(q.relative_to(copy))]['mode']);q=copy/'.extra';q.write_text('extra');check('unexpected_member',False);q.unlink();a=args.copy();a[4]='0'*64;check('wrong_manifest_anchor',False,a);q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'CONTROL');check('changed_report',False);q.write_bytes(data);check('restored',True);assert snap(copy)==state0
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('external-drift.json',{'changed_required_originals':changed,'other_required_originals_unchanged':9,'required_parent_assessments_fixed_before_future_child_launches':True,'limits':'No claim that all external originals remained unchanged during child run.'});dump('copied-controls.json',{'cases':cases,'positive':2,'negative':5,'whole_actual_root_unchanged':True,'limits':'Manifest binds file membership/bytes, not empty directories, modes,hardlink count. Parent checked actual single links/snapshots separately.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':68,'whole_root_files':71,'subdirectories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':20,'source_bytes':sum(e['size'] for e in source),'primary_tar_selected_member':1,'primary_PDF_text_pairs':1,'render_members':3,'required_initial_identities':10,'required_originals_initially_stable':9,'changed_required_parent_originals':1,'history_exact_range_selections':9,'stable_named_originals':list(stable.values()),'artifact_cases':7,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; no independent correctness/contribution grade, fresh primary/visual proof reading or finite/formal suite.'})
 print(json.dumps({'payload':68,'files':71,'source_blobs':20,'stable_originals':14,'required_parent_drift':1,'artifact_cases':7}))
if __name__=='__main__':main()

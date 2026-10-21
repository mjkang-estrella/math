#!/usr/bin/env python3
"""Analytic151 local byte archive; no mathematical grade."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r151'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'295d36a51eae4f4173d69bebcebc7ff856182e91b2ef9375cd6c9471051a0a40','MANIFEST.json':'c091e065425a0bf28d5e03ce8f20fa33346df910ab31c45999849f4543a2674c','REPORT.md':'fc541464bbcaa51819b7ba65d0a068c01a785554dab445708b0c2f7977b80c57'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='685091f2ffd00e2abab4e0dba8b02d5cbaa1ce47' and len(read(B/'tasks.json')['tasks'])==530
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':530,'task_index':527,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']=='r151-exact-files-v1' and len(m['files'])==59
 rows={e['path']:e for e in m['files']};assert len(rows)==59 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 dirs=[n for n,e in before.items() if e['kind']=='directory']
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'SOURCE-AUTH.json');assert len(source)==14 and len({e['canonical_path'] for e in source})==14 and sum(e['size'] for e in source)==318030
 for e in source:
  q=ROOT/e['selected_path'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==2;singles=archives=members=0
 for e in primary:
  q=ROOT/'private/primary'/(e['id']+'.incoming');data=q.read_bytes();assert len(data)==e['incoming_size'] and sha(q)==e['incoming_sha256'] and len(e['selected_members'])==1
  a=e['selected_members'][0];p=ROOT/a['selected_path'];assert p.stat().st_size==a['size'] and sha(p)==a['sha256']
  if a['member']=='single source stream':assert gzip.decompress(data)==p.read_bytes();singles+=1
  else:
   with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as tf:
    member=tf.getmember(a['member']);assert member.isfile() and tf.extractfile(member).read()==p.read_bytes()
   archives+=1
  members+=1
 assert members==2 and singles==archives==1
 originals=read(ROOT/'ORIGINALS-AUTH.json');assert len(originals)==13;stable=[]
 for e in originals:
  p=P/e['original_path'];q=ROOT/e['selected_path'];assert p.stat().st_size==q.stat().st_size==e['size'] and sha(p)==sha(q)==e['sha256'] and p.read_bytes()==q.read_bytes()
  stable.append({'path':e['original_path'],'bytes':e['size'],'sha256':e['sha256']})
 q=ROOT/'private/acceptance-section.md';assert q.read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 excerpt={'original_path':'frontier/NEW-TEN-2026-10-14.md','selected_path':'private/acceptance-section.md','sha256':sha(q),'limit':'Selected acceptance section only,no whole-journal identity.'}
 auth=read(ROOT/'private/authentication-replay.json');assert auth['pinned_objects']==14 and auth['original_copies']==13 and auth['primary_incoming_objects']==auth['primary_selected_members']==2
 ctl=read(ROOT/'private/control-results.json');fixture=ROOT/'private/controls'
 assert len(ctl['cases'])==6 and all((e['returncode']==0)==e['expected_pass'] and e['read_only_observed'] for e in ctl['cases'])
 assert all(sha(fixture/n)==v for n,v in ctl['fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 for a,b in ctl['selection'].items():assert (fixture/a).read_bytes()==(ROOT/b).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic151-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'scripts/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/SESSION.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact only.Manifest does not bind empty directories/modes;parent snapshots additionally observe subdirectories,modes,links,except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':14,'source_bytes':318030,'primary_received_objects':2,'primary_single_gzip_sources':1,'primary_tar_archives':1,'independently_reconstructed_members':2,'stable_whole_original_copies':13,'selected_acceptance_section':1,'selected_fixture_members':2,'limits':'Local byte/path/member authentication only.No fresh protected semantic reading,remote retrieval or transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':59,'whole_root_files':62,'subdirectories':len(dirs),'source_blobs':14,'primary_received_objects':2,'primary_members':2,'stable_named_originals':stable,'selected_original_excerpts':[excerpt],'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical/formal/numerical suite or grade.Manifest has no directory list;parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':62,'payload':59,'subdirectories':len(dirs),'source_blobs':14,'primary_objects':2,'primary_members':2,'whole_copies':13,'excerpt':1,'artifact_cases':6}))
if __name__=='__main__':main()

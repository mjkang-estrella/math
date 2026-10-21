#!/usr/bin/env python3
"""Analytic150 artifact authentication, not a mathematical review."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r150'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'15a5ef98f62e41651b8ae4430232778455023d965c52b27bdbbb0e6b020bb9df','MANIFEST.json':'3b80fe8c2cca863140a2f711f4ab5493e625884291740fb1d7de9a5d8b61920f','REPORT.md':'a4a393495525e02c3fee71aad957da70f43565470d9221a2da06acb541e9f954'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='e8fef7d32ff171c77d208f111d97adaa18bdf746' and len(read(B/'tasks.json')['tasks'])==527
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':527,'task_index':524,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root;excludes root-directory mode.Not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['version']==1 and m['envelopes']==list(ANCHORS) and len(m['files'])==59
 rows={e['path']:e for e in m['files']};assert len(rows)==59 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 dirs=[n for n,e in before.items() if e['kind']=='directory']
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'SOURCE-AUTH.json');assert source['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and source['tree_sha256']==sha(tp)
 source=source['objects'];assert len(source)==11 and sum(e['size'] for e in source)==69906
 prefix='preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/'
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(prefix) and p.endswith(('.tex','.bib'))}
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==5;members=0;singles=0;archives=0
 for e in primary:
  q=ROOT/e['incoming_copy'];data=q.read_bytes();assert len(data)==e['incoming_size'] and sha(q)==e['incoming_sha256']
  if len(e['selected_members'])==1 and e['selected_members'][0]['member']=='single source':
   a=e['selected_members'][0];p=ROOT/a['copy'];assert gzip.decompress(data)==p.read_bytes();singles+=1
  else:
   with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as tf:
    for a in e['selected_members']:
     p=ROOT/a['copy'];node=tf.getmember(a['member']);assert node.isfile() and tf.extractfile(node).read()==p.read_bytes()
   archives+=1
  for a in e['selected_members']:
   p=ROOT/a['copy'];assert p.stat().st_size==a['size'] and sha(p)==a['sha256'];members+=1
 assert members==7 and singles==2 and archives==3
 incoming=read(ROOT/'ORIGINALS-AUTH.json');assert len(incoming)==11;stable=[];excerpts=[]
 for e in incoming:
  q=ROOT/e['selected_copy'];p=P/e['original'];assert sha(q)==e['copy_sha256']
  if e['selection']=='whole original':
   assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and p.read_bytes()==q.read_bytes();stable.append({'path':e['original'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  else:assert e['original']=='frontier/NEW-TEN-2026-10-14.md' and q.stat().st_size==e['copy_size'] and q.read_bytes() in p.read_bytes();excerpts.append(e)
 assert len(stable)==10 and len(excerpts)==1
 auth=read(ROOT/'ARTIFACT-CHECKS.json');assert auth['canonical_pinned_objects_recomputed']==11 and auth['incoming_primary_objects']==5 and auth['selected_members_compared_to_incoming']==7 and auth['whole_original_copies_compared']==10
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected'
 assert len(ctl['cases'])==6 and all((e['exit_code']==0)==e['expected_accept'] and e['read_only_snapshot_unchanged'] for e in ctl['cases'])
 assert all(sha(fixture/n)==v for n,v in ctl['independent_detached_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert all(sha(P/p)==v for p,v in ctl['selected_originals'].items())
 assert (fixture/'original-prose/GAPS.md').read_bytes()==(ROOT/'GAPS.md').read_bytes() and (fixture/'protected-source/variance.tex').read_bytes()==(ROOT/'private/pinned-source/variance.tex').read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic150-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/SESSION.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact only.Manifest does not bind empty directories/modes;parent snapshots additionally observe subdirectories,modes,links,except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':11,'source_bytes':69906,'primary_incoming_objects':5,'primary_tar_archives':3,'primary_single_gzip_sources':2,'independently_reconstructed_selected_members':7,'stable_whole_original_copies':10,'selected_acceptance_section':1,'selected_fixture_payloads':2,'limits':'Local bytes/path/decompressed membership only.No fresh remote/protected-body semantic reading or full transitive/PDF/render attestation.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':59,'whole_root_files':62,'subdirectories':len(dirs),'source_blobs':11,'primary_received_objects':5,'primary_members':7,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical/formal/numerical suite or grade.Manifest has no directory list.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':62,'payload':59,'subdirectories':len(dirs),'source_blobs':11,'primary_objects':5,'primary_members':7,'stable_whole_copies':10,'excerpts':1,'artifact_cases':6}))
if __name__=='__main__':main()

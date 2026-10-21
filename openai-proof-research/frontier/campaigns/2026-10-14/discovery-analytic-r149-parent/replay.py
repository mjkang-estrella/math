#!/usr/bin/env python3
"""Analytic149 local artifact authentication; no mathematical grade."""
import datetime, fnmatch, gzip, hashlib, importlib.util, io, json, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r149'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'2510945624cc7db35adede82b1dc3c4285ddfce19d503363f6ae3e8041824e09','MANIFEST.json':'99739fec87c582b8ef583a43d97b558f5ffd23e3c7ec9ff05a380fa1f1d0d950','REPORT.md':'5b720c5d54c203064d891cf9a5179cc9f15a5afc26286de0d4456a34d791ca90'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='a3c1162e34cfc0b2247c7740048c7c28b27c2d21' and len(read(B/'tasks.json')['tasks'])==524
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':524,'task_index':521,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root, excluding root-directory mode; no historical whole-project/OS isolation claim.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']=='r149-exact-payload-v1' and m['outside_envelopes']==list(ANCHORS) and len(m['files'])==83
 rows={e['path']:e for e in m['files']};assert len(rows)==83 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 dirs=[n for n,e in before.items() if e['kind']=='directory']
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'SOURCE-AUTH.json');assert len(source)==32 and sum(e['tree_size'] for e in source)==229924
 prefixes={e['canonical_path'].split('/')[1] for e in source};assert len(prefixes)==3
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.split('/')[1] in prefixes and p.endswith(('.tex','.bib'))}
 globs=read(ROOT/'private/exclusions.json')['active_and_recent_literal_globs'];assert len(globs)==49
 for e in source:
  q=ROOT/e['selected_path'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['tree_size']==node['size'] and sha(q)==e['sha256']
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['pinned_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
  assert not any(fnmatch.fnmatchcase(e['canonical_path'].lower(),p.lower()) for p in globs)
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==4;members=0;archives=0;singles=0
 for e in primary:
  q=ROOT/'private/primary'/e['id']/'incoming.bin';data=q.read_bytes()
  assert len(data)==e['incoming_size'] and sha(q)==e['incoming_sha256'] and e['url']=='https://arxiv.org/src/'+e['id']
  assert len(e['members'])==1
  for a in e['members']:
   p=ROOT/a['selected_path'];assert p.stat().st_size==a['size'] and sha(p)==a['sha256']
   if a['member']=='single decompressed source':assert gzip.decompress(data)==p.read_bytes();singles+=1
   else:
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as tf:
     member=tf.getmember(a['member']);assert member.isfile() and tf.extractfile(member).read()==p.read_bytes()
    archives+=1
   members+=1
 assert members==4 and archives==2 and singles==2
 incoming=read(ROOT/'ORIGINALS-AUTH.json');assert len(incoming)==17;stable=[];excerpts=[]
 for e in incoming:
  q=ROOT/e['selected_path'];assert sha(q)==e['selected_sha256']
  if e['selected_kind']=='whole copy':
   p=P/e['original_path'];assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and p.read_bytes()==q.read_bytes()
   stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  else:
   assert e['original_path']=='frontier/NEW-TEN-2026-10-14.md' and q.stat().st_size==e['selected_size'] and (P/e['original_path']).read_bytes().startswith(q.read_bytes())
   excerpts.append(e)
 assert len(stable)==16 and len(excerpts)==1
 auth=read(ROOT/'AUTH-CHECK.json');assert auth['canonical_sources_matched']==32 and auth['primary_incoming_objects_matched']==auth['primary_selected_members_byte_compared']==4 and auth['whole_original_copies_byte_compared']==16 and auth['selected_acceptance_prefixes_only']==1
 ctl=read(ROOT/'controls/results.json');fixture=ROOT/'private/copied-controls'
 assert len(ctl['cases'])==6 and all(e['accepted']==e['expected'] and e['readonly_snapshot_equal'] for e in ctl['cases'])
 assert all(sha(fixture/n)==v for n,v in ctl['fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert (fixture/'original-note.md').read_bytes()==(ROOT/ctl['original_note']).read_bytes()
 assert (fixture/'protected-source.tex').read_bytes()==(ROOT/ctl['protected_source_original']).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic149-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy)
  args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/START.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only. Manifest does not bind empty directories/modes; parent snapshots additionally observe subdirectories,modes,links,except root-directory mode.'})
 dump('input-authentication.json',{'canonical_source_blobs':32,'canonical_source_bytes':229924,'primary_incoming_objects':4,'primary_tar_archives':2,'primary_single_gzip_sources':2,'independently_reconstructed_selected_members':4,'stable_whole_original_copies':16,'selected_acceptance_prefix':1,'selected_fixture_members':2,'limits':'Local bytes/paths/decompressed membership only; no fresh remote or protected-body semantic reading, no PDF/render or full transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':83,'whole_root_files':86,'subdirectories':len(dirs),'source_blobs':32,'primary_received_objects':4,'independently_reconstructed_primary_members':4,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive,not mathematical/formal/numerical suite or independent grade. Manifest excludes only three envelopes and does not bind empty directories. Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':86,'payload':83,'subdirectories':len(dirs),'source_blobs':32,'primary_objects':4,'primary_members':4,'stable_whole_copies':16,'excerpts':1,'artifact_cases':6}))
if __name__=='__main__':main()

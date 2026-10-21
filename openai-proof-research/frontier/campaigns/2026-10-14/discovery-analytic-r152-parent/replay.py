#!/usr/bin/env python3
"""Analytic152 local archive byte authentication and complete-copy controls."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r152'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'c2b12c2b17641dc86fbadca5129c758c3c8eab4ea693632726374339a892e535','MANIFEST.json':'9e3c66584c42b1b91ec448d1fca6c3dcbf43d71a1df68715d9291cd024ba291e','REPORT.md':'aca90ccbfb34765338cf50523964b3109db0ded468bd7908376dfd77480178d4'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==533
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root,excluding root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==77;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['bytes'] and sha(ROOT/e['path'])==e['sha256']
 auth=read(ROOT/'SOURCE-AUTH.json');tp=P/'sources/preprints-tree.json';assert sha(tp)==auth['tree_sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=auth['objects'];assert len(source)==19 and sum(e['bytes'] for e in source)==490431
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 pa=read(ROOT/'PRIMARY-AUTH.json');incoming=pa['incoming'];single=pa['canonical_incoming_and_selection'];assert len(incoming)==2 and len(single)==3 and len(pa['selected_members'])==8;members=0
 for e in incoming:
  q=ROOT/'private/primary'/(e['version']+'.incoming');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'];selected=[s for s in pa['selected_members'] if s['incoming_version']==e['version']]
  with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as archive:
   for s in selected:
    q=ROOT/s['local'];assert q.stat().st_size==s['bytes'] and sha(q)==s['sha256'] and archive.extractfile(s['member']).read()==q.read_bytes();members+=1
 for e in single:
  q=ROOT/'private/primary'/(e['version']+'.incoming');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'];assert len(e['members'])==1;s=e['members'][0];data=gzip.decompress(q.read_bytes());q=ROOT/s['local'];assert q.stat().st_size==s['bytes'] and sha(q)==s['sha256'] and q.read_bytes()==data;members+=1
 assert members==11
 originals=read(ROOT/'ORIGINALS-AUTH.json')['records'];assert len(originals)==13;stable=[]
 for e in originals:
  p=P/e['original_project_relative_path'];q=ROOT/e['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['bytes'] and sha(p)==sha(q)==e['sha256'];stable.append({'path':e['original_project_relative_path'],'bytes':e['bytes'],'sha256':e['sha256']})
 excerpt=ROOT/'private/acceptance-section.txt';assert excerpt.read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'CONTROL-RESULTS.json');fixture=ROOT/'private/controls';assert len(ctl['results'])==6 and all((e['exit']==0)==e['expected_accept'] and e['readonly_bytes_unchanged'] for e in ctl['results'])
 assert all(sha(fixture/n)==ctl['copied_selection_anchors'][k] for n,k in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]) and len(read(fixture/'MANIFEST.json')['files'])==2
 note_matches=[p.relative_to(ROOT).as_posix() for p in (ROOT/'notes').iterdir() if p.is_file() and p.read_bytes()==(fixture/'initial-note.md').read_bytes()];source_matches=[e['local'] for e in source if (ROOT/e['local']).read_bytes()==(fixture/'pinned-main.tex').read_bytes()];assert len(note_matches)==len(source_matches)==1
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic152-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[7]='0'*64;check('wrong_report_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dirs=len([e for e in before.values() if e['kind']=='directory'])
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact regular-file membership/bytes,not empty-directory membership/modes.Parent snapshots additionally observe directories/modes/links except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':19,'source_bytes':490431,'primary_received_objects':5,'primary_tar_objects':2,'primary_single_gzip_objects':3,'independently_reconstructed_selected_members':11,'stable_whole_original_copies':13,'selected_acceptance_excerpt':1,'fixture_original_note':note_matches[0],'fixture_original_source':source_matches[0],'limits':'Local byte/path/member authentication only.No fresh protected semantic reading,source/primary PDF or visual/transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':77,'whole_root_files':80,'subdirectories':dirs,'source_blobs':19,'primary_received_objects':5,'primary_selected_members':11,'stable_named_originals':stable,'selected_acceptance_excerpt':{'path':'private/acceptance-section.txt','sha256':sha(excerpt)},'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact checks only,no mathematical/contribution grade or finite/formal suite.'})
 print(json.dumps({'payload':77,'files':80,'subdirs':dirs,'source_blobs':19,'primary_objects':5,'primary_members':11,'stable_originals':13,'artifact_cases':6}))
if __name__=='__main__':main()

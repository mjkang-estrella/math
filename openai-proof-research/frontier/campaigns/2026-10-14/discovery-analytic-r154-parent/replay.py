#!/usr/bin/env python3
"""Authenticate Analytic154's completed packet; artifact checks only."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r154'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b37b941e9d86d7f1076dc976357979b36863dc72e7b318aee07d42d792e92768','MANIFEST.json':'b729e18276ee8963ace8763a3838e38ecadf6766c47d4c4b2ae6854d9b0820ac','REPORT.md':'a77dda92ecb9e67675297c3b103ce8b2bcd74297d7f18b745a86b90416eacdeb'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==539
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==71;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-auth.json');assert len(source)==18 and sum(e['size'] for e in source)==402447
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary/auth.json');good=[e for e in primary if 'incoming_sha256' in e];assert len(good)==6 and len(primary)==7;members=[]
 for e in good:
  q=ROOT/'private/primary'/e['version'].replace('/','-')/'incoming';assert q.stat().st_size==e['incoming_size'] and sha(q)==e['incoming_sha256']
  for s in e['selected']:assert (ROOT/s['copy']).stat().st_size==s['size'] and sha(ROOT/s['copy'])==s['sha256']
  try:
   with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as a:
    for s in e['selected']:assert a.extractfile(s['member']).read()==(ROOT/s['copy']).read_bytes()
   kind='tar'
  except tarfile.ReadError:
   assert len(e['selected'])==1 and gzip.decompress(q.read_bytes())==(ROOT/e['selected'][0]['copy']).read_bytes();kind='single_gzip'
  members.append({'version':e['version'],'container':kind,'selected_members':len(e['selected'])})
 originals=read(ROOT/'private/required-originals.json')+read(ROOT/'private/history-auth.json');assert len(originals)==13;stable=[]
 for e in originals:
  p=P/e['original_path'];q=ROOT/e['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['size'] and sha(p)==sha(q)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['size'],'sha256':e['sha256']})
 assert (ROOT/'private/acceptance.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selection';assert len(ctl['checks'])==6 and all(e['read_only'] and e['behaved_as_expected'] and (e['returncode']==0)==e['expect_accept'] for e in ctl['checks']);assert all(sha(fixture/n)==v for n,v in ctl['detached_selection_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 ownmatch=[p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.md') if 'private' not in p.relative_to(ROOT).parts and p.read_bytes()==(fixture/'calculation.md').read_bytes()];srcmatch=[e['canonical_path'] for e in source if (ROOT/e['selected_copy']).read_bytes()==(fixture/'protected-source.tex').read_bytes()];assert len(ownmatch)==len(srcmatch)==1
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic154-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'scripts/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[6]='0'*64;check('wrong_report_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items());dirs=len([e for e in before.values() if e['kind']=='directory'])
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; exact regular-file membership/bytes, not empty directories or modes. Parent snapshot observes directories/modes/links except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':18,'source_bytes':402447,'primary_received_objects':6,'primary_reconstructed_sources':members,'stable_whole_original_copies':13,'selected_acceptance_excerpt':1,'selected_control_original_note':ownmatch,'selected_control_source_paths':srcmatch,'limits':'Local byte/path/member authentication only. No fresh protected semantic/source/primary/transitive reading; no numerical or formal suite.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':71,'whole_root_files':74,'subdirectories':dirs,'source_blobs':18,'primary_received_objects':6,'primary_selected_source_members':6,'stable_named_originals':stable,'selected_acceptance_excerpt':1,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; no independent mathematical/contribution grade.'})
 print(json.dumps({'payload':71,'files':74,'subdirs':dirs,'source_blobs':18,'primary_objects':6,'members':members,'stable_originals':13,'artifact_cases':6}))
if __name__=='__main__':main()

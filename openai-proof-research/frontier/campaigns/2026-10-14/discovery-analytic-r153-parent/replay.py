#!/usr/bin/env python3
"""Analytic153 completed archive authentication; artifact checks only."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r153'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'2cf0d2a3d8e473937d71bed63de676b86b6211fde7fbb783cc031bc2a5beaac3','MANIFEST.json':'50b2896ec19bb1f3c3bc7a3c2c4a49608f125d983e8aabd4f931f0e87a03aef8','REPORT.md':'809a768262533ecf493a4887e52095fabedaae1c869a3de41d41acefec961fe5'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==536
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==107;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['bytes'] and sha(ROOT/e['path'])==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'SOURCE-AUTH.json');assert len(source)==27 and sum(e['bytes'] for e in source)==356730
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==3;members=[]
 for e in primary:
  q=ROOT/'private/primary'/e['key']/('author.pdf' if e['key']=='gw' else 'incoming.bin');assert q.stat().st_size==e['incoming']['bytes'] and sha(q)==e['incoming']['sha256']
  for s in e['selected']:
   p=ROOT/s['path'];assert p.stat().st_size==s['bytes'] and sha(p)==s['sha256']
  if e['key']!='gw':
   try:
    with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as a:
     for s in e['selected']:assert a.extractfile(s['member']).read()==(ROOT/s['path']).read_bytes()
    kind='tar'
   except tarfile.ReadError:
    assert len(e['selected'])==1 and gzip.decompress(q.read_bytes())==(ROOT/e['selected'][0]['path']).read_bytes();kind='single_gzip'
   members.append({'key':e['key'],'container':kind,'selected_members':len(e['selected'])})
 originals=read(ROOT/'ORIGINALS-AUTH.json');assert len(originals)==11;stable=[]
 for e in originals:
  p=P/e['original'];q=ROOT/e['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['bytes'] and sha(p)==sha(q)==e['sha256'];stable.append({'path':e['original'],'bytes':e['bytes'],'sha256':e['sha256']})
 excerpt=ROOT/'private/acceptance.txt';assert excerpt.read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected-baseline';assert len(ctl['cases'])==6 and all(e['exit_code']==e['expected'] and e['copy_unchanged'] for e in ctl['cases']);assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert (fixture/'own-note.md').read_bytes()==(ROOT/'notes/GEOMETRIC-CHECKS.md').read_bytes();assert (fixture/'private-source.tex').read_bytes()==(ROOT/source[0]['local']).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic153-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[6]='0'*64;check('wrong_report_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items());dirs=len([e for e in before.values() if e['kind']=='directory'])
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact regular-file membership/bytes,not empty-directory membership/modes.Parent snapshots additionally observe directories/modes/links except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':27,'source_bytes':356730,'primary_received_objects':3,'primary_reconstructed_sources':members,'primary_pdf_text_pairs':1,'render_members':1,'stable_whole_original_copies':11,'selected_acceptance_excerpt':1,'selected_fixture_members':2,'compiled_own_payload':'tools/__pycache__/isolation.cpython-314.pyc is bound in original seal,not executed or staged','limits':'Local byte/path/member authentication only.No fresh protected semantic/PDF/visual/transitive reading.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':107,'whole_root_files':110,'subdirectories':dirs,'source_blobs':27,'primary_received_objects':3,'primary_selected_source_members':2,'primary_pdf_text_pairs':1,'render_members':1,'stable_named_originals':stable,'selected_acceptance_excerpt':1,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact checks only,no independent mathematical/contribution grade or numerical/formal suite.'})
 print(json.dumps({'payload':107,'files':110,'subdirs':dirs,'source_blobs':27,'primary_objects':3,'reconstructed_sources':members,'pdf_text_pairs':1,'renders':1,'stable_originals':11,'artifact_cases':6}))
if __name__=='__main__':main()

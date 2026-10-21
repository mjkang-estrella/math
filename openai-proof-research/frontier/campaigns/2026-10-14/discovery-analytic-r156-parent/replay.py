#!/usr/bin/env python3
"""Analytic156 completed archive authentication; no mathematical gate."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r156'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'23a24ba7cf8396b4947d56d031843072528c944512993242694ae9b5bec5e6fc','MANIFEST.json':'657264a688540a3eb566b5109ebbd8875c2f47f384341611e244f362650ee9e5','REPORT.md':'9b939725ff5d07d9329031485ce5947e750119abbd209ebaec5deda6097ccbf9'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==547
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'});st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==85;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_nlink==1
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-auth.json')+read(ROOT/'private/companion-auth.json');assert len(source)==32 and sum(e['size'] for e in source)==1235844
 for e in source:
  q=ROOT/e['selected'];data=q.read_bytes();node=entries[e['canonical']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 primary=read(ROOT/'private/primary-auth.json');assert len(primary)==2
 for e in primary:
  version=e['url'].rsplit('/',1)[1];q=ROOT/'private/primary'/version/'incoming';s=e['members'][0];p=q.parent/'selected.tex';assert q.stat().st_size==e['incoming_size'] and sha(q)==e['incoming_sha256'] and p.stat().st_size==s['size'] and sha(p)==s['sha256'] and gzip.decompress(q.read_bytes())==p.read_bytes()
 e=read(ROOT/'private/primary/1812.11616v2/auth.json');q=ROOT/'private/primary/1812.11616v2/incoming';assert q.stat().st_size==e['incoming_size'] and sha(q)==e['incoming_sha256']
 with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as tar:
  for s in e['members']:
   p=q.parent/'selected'/s['name'];assert p.stat().st_size==s['size'] and sha(p)==s['sha256'] and tar.extractfile(s['name']).read()==p.read_bytes()
 e=read(ROOT/'private/primary/JSW/auth.json');q=ROOT/'private/primary/JSW/jsw.pdf';assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file() and len(list(q.parent.glob('page*.png')))==2
 e=next(x for x in read(ROOT/'private/primary/Seeger1988/alternate-attempts.json') if 'sha256' in x);q=ROOT/'private/primary/Seeger1988/alternate-1';assert q.stat().st_size==e['size']==3038 and sha(q)==e['sha256'] and not q.read_bytes().startswith(b'%PDF')
 stable=[]
 for e in read(ROOT/'private/r155-read-receipts.json'):
  p=P/e['path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['path'],'bytes':e['size'],'sha256':e['sha256']})
 assert len(stable)==10
 for e in read(ROOT/'private/operative-history-identities.json'):
  p=P/e['original'];q=ROOT/e['selection'];assert p.stat().st_size==e['original_size']==q.stat().st_size==e['selection_size'] and sha(p)==e['original_sha256']==sha(q)==e['selection_sha256'];stable.append({'path':e['original'],'bytes':e['original_size'],'sha256':e['original_sha256']})
 e=read(ROOT/'private/history/iterations/i66-dispersive-equation-discovery-7-52.identity.json');p=P/e['original_path'];assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];copies=[q for q in (ROOT/'private/history/iterations').iterdir() if q.is_file() and not q.name.endswith('.json')];assert len(copies)==1;data=copies[0].read_bytes();a,b=e['selected_lines'];assert hashlib.sha256(data).hexdigest()==e['selected_sha256'] and data==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b]);stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']});assert len(stable)==13
 assert (ROOT/'private/acceptance-excerpt.md').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected-original';assert len(ctl['cases'])==5 and all(e['accepted']==e['expected_accept'] for e in ctl['cases']) and ctl['originals_unchanged'];assert all(sha(fixture/n)==v for n,v in ctl['selected_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 for e in ctl['originals']:assert (P/e['original_path']).stat().st_size==e['original_size'] and sha(P/e['original_path'])==sha(fixture/e['selected_path'])==e['original_sha256']==e['selected_sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic156-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy)
  for p in [copy,*copy.rglob('*')]:p.chmod(p.stat().st_mode|0o200)
  copy_before=snap(copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q.chmod(copy_before['notes/FEASIBILITY.md']['mode']);q=copy/'.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[6]='0'*64;check('wrong_report_anchor',False,wrong);check('restored',True);assert snap(copy)==copy_before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items());dirs=sum(e['kind']=='directory' for e in before.values())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Manifest binds file membership/bytes,not hardlink count,empty directories or modes. Actual original single-link files checked separately;copied permission changes confined to disposable fixture.'})
 dump('input-authentication.json',{'source_blobs':32,'source_bytes':1235844,'primary_single_gzip_sources':2,'primary_tar_selected_members':1,'primary_pdf_text_pairs':1,'render_members':2,'nonPDF_failed_original_response':1,'stable_required_original_identities':10,'stable_operative_history_whole_copies':2,'stable_range_original_identities':1,'selected_acceptance_excerpt':1,'limits':'Local byte/path/member authentication only;no fresh protected source/primary/PDF/visual/transitive reading or mathematical/formal suite. Original Seeger1988 proof remains unread.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':85,'whole_root_files':88,'subdirectories':dirs,'source_blobs':32,'primary_single_gzip_sources':2,'primary_tar_selected_members':1,'primary_pdf_text_pairs':1,'render_members':2,'stable_named_originals':stable,'required_identity_only_originals':10,'whole_operative_history_copies':2,'exact_history_range_selections':1,'selected_acceptance_excerpt':1,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;no independent mathematical/contribution grade or new finite/formal experiment.'})
 print(json.dumps({'payload':85,'files':88,'dirs':dirs,'source_blobs':32,'primary_gzip_sources':2,'tar_member':1,'PDF_text_pair':1,'renders':2,'stable_originals':13,'artifact_cases':6}))
if __name__=='__main__':main()

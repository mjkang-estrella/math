#!/usr/bin/env python3
"""Structural163 artifact authentication; no mathematical grade."""
import datetime,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r163'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'c6a50f62db37640b812386ca621b8b8eb1f1fd62265179dfde8bb0bba4dd1612','MANIFEST.json':'bcfed7dcb4a6bb38390ca85c2a092e9e87a26ab655d3c2ed17d26e67e0614f6b','REPORT.md':'1540671d1e6a18a80c1746d150a6b3d8506efeeac46f3ab7b1fc5f47bcbdc8db'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==552
 before=snap(ROOT);root_mode=stat.S_IMODE(ROOT.stat().st_mode);m=read(ROOT/'MANIFEST.json');assert len(m['files'])==58 and len(m['directories'])==20 and root_mode==m['root_mode']==0o555
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256'] and stat.S_IMODE((ROOT/n).stat().st_mode)==e['mode'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-authentication.json');assert len(source)==24
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable=[]
 for e in read(ROOT/'private/incoming-original-identities.json'):
  p=P/e['original_path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['bytes'],'sha256':e['sha256']})
 assert len(stable)==11 and (ROOT/'private/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary-acquisitions.json');success=[e for e in primary if 'sha256' in e];assert len(success)==2 and len(primary)==3
 for e in success:
  q=ROOT/'private/primary'/e['file'];assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file()
 e=read(ROOT/'private/primary-acquisition02.json');q=ROOT/'private/primary/oblivious-v2.pdf';assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file()
 ctl=read(ROOT/'evidence/copied-controls.json');assert len(ctl['controls'])==11 and all(e['expected']==e['observed']['exit'] for e in ctl['controls']);fixture=ROOT/'private/controls/base';assert sha(fixture/'notes.txt')==sha(ROOT/'notes/02-integrated-calculations.md') and sha(fixture/'private/setup.tex')==sha(ROOT/'private/source/uniform/build/manuscript/setup.tex')
 diag=read(ROOT/'evidence/transform-diagnostic.json');assert len(diag['rows'])==24 and diag['parameters']['r']=='11/18' and diag['missing_length_example']=={'naive':'445/648','correct':'121/324'}
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural163-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);initial=snap(copy);args=[str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);rm=stat.S_IMODE(copy.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(copy/'evidence/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state and stat.S_IMODE(copy.stat().st_mode)==rm;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
  check('unchanged',True);q=copy/'notes/00-start.md';data=q.read_bytes();q.chmod(0o644);q.write_bytes(data+b'CONTROL');q.chmod(0o444);check('changed_member',False);q.parent.chmod(0o755);q.unlink();q.parent.chmod(0o555);check('missing_member',False);q.parent.chmod(0o755);q.write_bytes(data);q.chmod(0o444);q.parent.chmod(0o555);copy.chmod(0o755);q=copy/'.extra';q.write_text('extra');copy.chmod(0o555);check('unexpected_member',False);copy.chmod(0o755);q.unlink();copy.chmod(0o555);a=args.copy();a[6]='0'*64;check('wrong_report_anchor',False,a);copy.chmod(0o755);check('changed_root_mode',False);copy.chmod(0o555);check('restored',True);assert snap(copy)==initial
  for b,ds,fs in os.walk(copy):Path(b).chmod(0o755)
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==root_mode and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':root_mode});dump('copied-controls.json',{'cases':cases,'positive':2,'negative':5,'whole_actual_root_unchanged':True,'limits':'Artifact bytes/membership/modes only,not mathematics; actual single links checked separately.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':58,'whole_root_files':61,'subdirectories':20,'source_blobs':24,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':3,'failed_primary_acquisitions':1,'stable_named_originals':stable,'stable_original_identities':11,'finite_diagnostic_rows':24,'finite_diagnostic_not_rerun':True,'artifact_cases':7,'whole_actual_root_unchanged':True,'limits':'No independent mathematical gate, fresh primary/visual proof reading or formal suite.'})
 print(json.dumps({'payload':58,'files':61,'dirs':20,'source_blobs':24,'primary_pairs':3,'stable_originals':11,'artifact_cases':7}))
if __name__=='__main__':main()

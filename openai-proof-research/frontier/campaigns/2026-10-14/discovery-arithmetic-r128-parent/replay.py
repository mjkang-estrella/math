#!/usr/bin/env python3
"""Authenticate Arithmetic128's completed research record; no mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r128'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'a5e272cbbc8dd23e7aea28e6e57b6acc2d8d9c5aa3f63ed6d1ea9e68ab9a1af3','MANIFEST.json':'1148c066555734488c3ad1560a89f4aa99de05f7601c1cc64812827f9af05c3f','REPORT.md':'9afdbf03c5e024571b45027ad1e221aafe957e65937d9c00cf1b05e3815bbe8f'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==548
 before=snap(ROOT);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==60 and len(m['directories'])==9 and {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/pinned-identities.json');assert len(source)==6
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['canonical']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 stable=[]
 for e in read(ROOT/'private/incoming-identities.json'):
  p=P/e['original'];q=ROOT/e['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['original_bytes']==e['copy_bytes'] and sha(p)==sha(q)==e['original_sha256']==e['copy_sha256'];stable.append({'path':e['original'],'bytes':e['original_bytes'],'sha256':e['original_sha256']})
 assert len(stable)==12 and (ROOT/'private/incoming/acceptance-section.md').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary-identities.json');success=[e for e in primary if 'sha256' in e];assert len(success)==5 and len(primary)-len(success)==2
 for e in success:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(q.with_suffix('.txt'))==e['text_sha256']
 renders=read(ROOT/'private/render-identities.json');assert len(renders)==4
 for e in renders:assert (ROOT/e['path']).stat().st_size==e['bytes'] and sha(ROOT/e['path'])==e['sha256']
 e=read(ROOT/'private/primary/bisbas-selection-identity.json');q=ROOT/'private/primary/bisbas-web-selection.json';assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256']
 ctl=read(ROOT/'private/copied-control-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['records'])==7 and all((e['returncode']==0)==e['expected_accept'] and e['read_only_before_after_equal'] for e in ctl['records']);assert sha(fixture/'payload/integrated-note.md')==sha(ROOT/'notes/integrated-salem-reduction.md')==ctl['note_copy_sha256'] and sha(fixture/'payload/verify.py')==sha(ROOT/'tools/verify.py')==ctl['verifier_copy_sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic128-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);initial=snap(copy);args=['--root',str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
  check('unchanged',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'CONTROL');check('changed_member',False);q.unlink();check('missing_member',False);q.write_bytes(data);q.chmod(initial[str(q.relative_to(copy))]['mode']);q=copy/'.extra';q.write_text('extra');check('unexpected_member',False);q.unlink();q=copy/'empty';q.mkdir();check('unexpected_empty_directory',False);q.rmdir();args2=args.copy();args2[5]='0'*64;check('wrong_manifest_anchor',False,args2);check('restored',True);assert snap(copy)==initial
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('copied-controls.json',{'cases':cases,'positive':2,'negative':5,'whole_actual_root_unchanged':True,'limits':'Exact file/directory membership, bytes and single links; manifest does not bind modes/timestamps.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':60,'whole_root_files':63,'subdirectories':9,'source_blobs':6,'source_bytes':sum(e['bytes'] for e in source),'primary_PDF_text_pairs':5,'render_members':4,'serialized_web_selection':1,'failed_primary_acquisitions':2,'stable_named_originals':stable,'whole_original_copies':12,'selected_acceptance_excerpt':1,'artifact_cases':7,'whole_actual_root_unchanged':True,'limits':'Artifact authentication only; no fresh source/primary/visual proof reading or independent mathematical gate.'})
 print(json.dumps({'payload':60,'files':63,'dirs':9,'source_blobs':6,'primary_pairs':5,'renders':4,'stable_originals':12,'artifact_cases':7}))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Read-only review adoption artifact replay;no fresh mathematical grade."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];AUTHOR=B/'fresh-analytic-discovery-r147'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'proof':{'FINAL.md':'d7f2e80554077c7a16e6ce3d56f7075c62b946f7332ed543f942fe895440b563','MANIFEST.json':'3d68e896912bc78e2752695b20e9bc16026b46e03d556b56ec4daad491238707','REPORT.md':'1fd239f3b2c5b61489d04814640c6cf0abd00b74e5f136b8e4716ddc78b62f69'},'contribution':{'FINAL.md':'eea86f9dde8bf1345d4f124f22ca10532ea73958b252932f96231fe1701b88b8','MANIFEST.json':'afa81fa56edcc3f1b7239f983d85d4eb390706dd01a38d5512d65e10b8cd9fe0','REPORT.md':'4d987707b311cc6951230512466946f76e68c94e4e5b6d86fe7968ad46ccd230'}}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P);assert len(read(B/'tasks.json')['tasks'])==518
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'task_count':518,'protected_unrelated_sha256':PROTECTED})
 author=snap(AUTHOR);assert author==read(O.parent/'observed-root.json')['root'];tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';entries={e['path']:e for e in tree['tree']}
 stable={};states={};reports={};controls={}
 for role,count,copies in [('proof',66,49),('contribution',110,50)]:
  root=B/('t360s147-'+role+'-r1');before=snap(root);states[role]=before;anchors=ANCHORS[role]
  st=read(O/(role+'-task-status.json'))['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in anchors.values());assert all(sha(root/n)==v for n,v in anchors.items())
  m=read(root/'MANIFEST.json');assert m['excluded_envelopes']==['FINAL.md','MANIFEST.json','REPORT.md'] and len(m['files'])==count
  rows={e['path']:e for e in m['files']};assert len(rows)==count and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(anchors)
  for n,e in rows.items():assert (root/n).stat().st_size==e['size'] and sha(root/n)==e['sha256']
  auth=read(root/'INPUT-AUTH.json');selected=auth['copies'] if role=='proof' else auth;assert len(selected)==copies;sources=0
  for e in selected:
   n=e.get('selected_copy',e.get('copy'));data=(root/n).read_bytes();p=P/e['original'];assert len(data)==e['size'] and sha(root/n)==e['sha256'] and p.read_bytes()==data
   stable[e['original']]={'path':e['original'],'bytes':e['size'],'sha256':e['sha256']}
   if 'canonical_path' in e:
    cp=e['canonical_path'];node=entries[cp];assert len(data)==node['size'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+cp;sources+=1
  assert sources==17
  primary=read(AUTHOR/'PRIMARY-AUTH.json');members=0
  for e in primary:
   p=root/e['incoming_path'];data=p.read_bytes();assert len(data)==e['size'] and sha(p)==e['sha256']
   for a in e['selected']:
    try:
     with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as ar:body=ar.extractfile(a['member']).read()
    except tarfile.ReadError:body=gzip.decompress(data)
    assert body==(root/a['copy']).read_bytes() and sha(root/a['copy'])==a['sha256'];members+=1
  assert members==3
  ctl=read(root/'CONTROL-RESULTS.json');assert len(ctl['controls'])==6 and all(e['expected_accept']==e['accepted'] and e['read_only_snapshot_match'] for e in ctl['controls'])
  fixture=root/('private/controls/fixture' if role=='proof' else 'private/controls/selection');assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items())
  fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==2
  for e in fm['files']:
   original=root/e['path'] if e['path']!='STATEMENT.md' else root/'private/author/STATEMENT.md'
   assert original.read_bytes()==(fixture/e['path']).read_bytes() and sha(original)==e['sha256']
  cases=[]
  with tempfile.TemporaryDirectory(prefix=role+'-copy-',dir=O) as temp:
   copy=Path(temp)/'packet';shutil.copytree(root,copy);args=[str(copy),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
   def check(label,want,custom=None):
    state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(role,label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'copy_unchanged':True,'stdout':r.stdout.strip(),'stderr_tail':r.stderr[-300:]})
   check('baseline_full_packet',True);p=copy/'REVIEW.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data);p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
  assert snap(root)==before;controls[role]=cases;reports[role]={'payload_files':count,'whole_root_files':count+3,'subdirectories':sum(e['kind']=='directory' for e in before.values()),'selected_copies':copies,'canonical_source_bodies':sources,'primary_incoming':4,'independent_primary_members':3,'parent_copied_cases':6,'negative_cases':4,'external_handoff_anchors':anchors}
 extra=[];root=B/'t360s147-contribution-r1';acquisitions=['comparator-acquisitions.json','earlier-formulations.json','hencl-recovery.json','new-acquisitions.json','version-recovery.json'];member_count=0;failures=[]
 for name in acquisitions:
  for e in read(root/'private/primary'/name):
   if 'error' in e:failures.append(e);continue
   p=root/'private/primary'/e['file'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];extra.append({'file':e['file'],'bytes':e['size'],'sha256':e['sha256'],'url':e['url']})
   sel=e.get('selected',[]);sel=[sel] if isinstance(sel,dict) else sel
   for a in sel:
    body=gzip.decompress(p.read_bytes());q=root/'private/primary'/(a['file'] if 'file' in a else e['file'].removesuffix('.source')+'/main.tex');assert body==q.read_bytes() and len(body)==a['size'] and sha(q)==a['sha256'];member_count+=1
 assert len(extra)==13 and member_count==5
 assert snap(AUTHOR)==author and all(snap(B/('t360s147-'+role+'-r1'))==states[role] for role in reports) and all(sha(P/p)==v for p,v in PROTECTED.items()) and all(sha(P/e['path'])==e['sha256'] for e in stable.values())
 dump('observed-roots.json',{'author':author,**states,'limits':'Current whole roots;root-directory modes excluded.Not historical isolation/read coverage.'});dump('copied-controls.json',{'roles':controls,'cases_total':12,'negative_cases_total':8,'all_calls_read_only':True,'actual_roots_unchanged':True})
 dump('input-authentication.json',{'roles':reports,'contribution_new_received_objects':extra,'contribution_new_selected_members':member_count,'recorded_failures':failures,'limits':'Byte/selection binding only.No fresh remote,protected-body semantic,PDF visual or extraction claim;failed/HTML/empty objects are not primary PDFs read.'})
 dump('replay.json',{'observed_utc':now,'roles':reports,'stable_named_originals':list(stable.values()),'unchanged_author_statement_sha256':sha(AUTHOR/'STATEMENT.md'),'unchanged_author_proof_sha256':sha(AUTHOR/'AUTHOR-PROOF.md'),'all_actual_roots_unchanged':True,'limits':'Artifact adoption checks only;independent mathematical/contribution verdicts come from role reviews,not hashes or controls.'})
 print(json.dumps({'proof_payload':66,'contribution_payload':110,'whole_files':69+113,'stable_selected_originals':len(stable),'canonical_source_bodies_per_role':17,'new_received_objects':13,'new_member_bindings':5,'parent_artifact_cases':12}))
if __name__=='__main__':main()

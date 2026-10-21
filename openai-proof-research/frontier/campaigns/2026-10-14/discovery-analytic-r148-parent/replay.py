#!/usr/bin/env python3
"""Completed analytic148 byte archive;no mathematical suite or independent grade."""
import datetime,gzip,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r148'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'f7ce5bbfdb2ee8a1c353fb4881f8afa37b5e192a68f940b57810f36cc639a8eb','MANIFEST.json':'2a67663c2a75f46847b7bc216d11881391b5a153f168dc8fa23fe2cc38733295','REPORT.md':'21c6de31aead804d717fee811625c3bb859b8743850fa14d730151f98623fba8'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P);assert len(read(B/'tasks.json')['tasks'])==521
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':521,'task_index':519,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root,excluding root-directory mode;not historical whole-project/OS provenance.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values());assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['excluded_envelopes']==list(ANCHORS) and len(m['files'])==61;rows={e['path']:e for e in m['files']};assert len(rows)==61 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'SOURCE-AUTH.json');assert len(source)==7;prefix='preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/';smooth='preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/'
 assert {e['canonical'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(prefix) and p.endswith('.tex')}|{smooth+'build/sections/01-introduction.tex',smooth+'build/sections/08-scalar-consequence.tex'}
 for e in source:
  data=(ROOT/e['selected']).read_bytes();node=entries[e['canonical']];assert len(data)==e['size']==node['size'] and sha(ROOT/e['selected'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==4;pdfs=members=extracts=0
 for e in primary:
  p=ROOT/e['incoming'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256']
  if e.get('is_pdf'):
   assert p.read_bytes().startswith(b'%PDF');pdfs+=1;a=e['selected_extraction'];assert (ROOT/a['path']).stat().st_size==a['size'] and sha(ROOT/a['path'])==a['sha256'];extracts+=1
  for a in e.get('members',[]):
   data=gzip.decompress(p.read_bytes());q=ROOT/a['selected'];assert data==q.read_bytes() and len(data)==a['size'] and sha(q)==a['sha256'];members+=1
 assert (pdfs,extracts,members)==(3,3,1)
 stable=[];excerpts=[];originals=read(ROOT/'ORIGINALS-AUTH.json')['files'];assert len(originals)==16
 for e in originals:
  q=ROOT/e['selected'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
  if e['selection'].startswith('whole original'):
   p=P/e['original'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  else:excerpts.append(e|{'limit':'Independent excerpt membership,not whole-copy/current-future mutable-original preservation.'})
 assert len(stable)==15 and len(excerpts)==1
 recheck=read(ROOT/'ORIGINALS-RECHECK.json');assert len(recheck['files'])==16 and all(e['matches_late_authentication'] for e in recheck['files'])
 ctl=read(ROOT/'CONTROL-RESULTS.json');fixture=ROOT/'private/copied-control';assert len(ctl['results'])==6 and all(e['snapshot_unchanged'] and (e['exit_code']==0)==e['expected_accept'] for e in ctl['results']) and ctl['independent_sha256sum_matches']
 assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items());fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==2
 for e in fm['files']:assert (ROOT/e['path']).read_bytes()==(fixture/e['path']).read_bytes() and sha(ROOT/e['path'])==e['sha256'] and (fixture/e['path']).stat().st_size==e['size']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic148-copy-',dir=O) as temp:
  copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);p=copy/'GAPS.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data);p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();wrong=args.copy();wrong[5]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only.Verifier rejects symlinks/nonregular/hardlinked files;does not bind modes or empty directories.'})
 dump('input-authentication.json',{'source_blobs':7,'primary_received_objects':4,'primary_pdfs':3,'primary_gzip_source':1,'independent_selected_member':1,'byte_bound_text_derivatives':3,'byte_bound_renders':2,'stable_whole_original_copies':15,'selected_excerpts':1,'selected_fixture_members':2,'limits':'Local byte/selection binding only;no fresh remote,protected-body semantic reading,PDF visual or extraction attestations.No inherited manifest seals a reduced selection.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':61,'whole_root_files':64,'subdirectories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':7,'primary_received_objects':4,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical numerical/formal suite or independent grade.Parent snapshots exclude root-directory mode;verifier omits modes/emptydirectories.'})
 print(json.dumps({'files':64,'payload':61,'source_blobs':7,'primary_objects':4,'selected_member':1,'stable_whole_copies':15,'excerpts':1,'artifact_cases':6}))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Structural157 archive authentication and redirected exact finite replay."""
import datetime,gzip,hashlib,importlib.util,io,json,re,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r157'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'177164433761692025e1753c75052e7e8163ef3e688533d815e924107848bb77','MANIFEST.json':'288dd8ee84b53bd9dd73cb23199f4ce1763be1791939d8fd0f0f4bea037e249a','REPORT.md':'190c4513e362d15c45732d27a90b373ebe9ccbbf5859e4b394637389ef829df1'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==531
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Observed sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==64 and len(m['directories'])==15
 assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])-{'.'}
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';tm=read(ROOT/'receipts/tree-identity.json');assert sha(tp)==tm['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source168-identities.json');assert len(source)==10
 prefix='preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/'
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(prefix) and p.endswith(('.md','.tex','.bib'))}
 for e in source:
  q=ROOT/e['selected_path'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 assert len(read(ROOT/'private/source168-recheck.json'))==10 and all(e['matches_initial_identity'] for e in read(ROOT/'private/source168-recheck.json'))
 primary=read(ROOT/'private/primary-incoming01.json')+read(ROOT/'private/primary-incoming02.json');members=0
 for e in primary:
  q=ROOT/'private'/e['name']/'incoming.bin';assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
  if e['name']=='lanini':
   data=gzip.decompress(q.read_bytes());assert len(e['selected'])==1
   assert data==(ROOT/e['selected'][0]['path']).read_bytes()
  else:
   with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as archive:
    for s in e['selected']:assert archive.extractfile(s['member']).read()==(ROOT/s['path']).read_bytes()
  for s in e['selected']:
   q=ROOT/s['path'];assert q.stat().st_size==s['size'] and sha(q)==s['sha256'];members+=1
 html=read(ROOT/'private/primary-incoming03.json');assert len(primary)==3 and members==4 and len(html)==2
 for e in html:
  q=ROOT/e['selected_path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 originals=read(ROOT/'private/incoming-original-identities.json');assert len(originals)==8;stable=[]
 for e in originals:
  p=P/e['path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['path'],'bytes':e['size'],'sha256':e['sha256']})
 selected=read(ROOT/'private/selected-membership.json');assert len(selected)==9;whole=0;excerpts=[]
 for e in selected:
  q=ROOT/e['path'];p=P/e['incoming_original_path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
  if e['selection']=='whole copy':assert p.read_bytes()==q.read_bytes();whole+=1
  else:assert q.read_bytes() in p.read_bytes();excerpts.append(e)
 assert whole==8 and len(excerpts)==1
 ctl=read(ROOT/'receipts/copied-controls.json');fixture=ROOT/'private/copied-fixture';assert len(ctl['results'])==8 and all(e['returncode']==e['expected_returncode'] and e['verifier_unchanged'] for e in ctl['results'])
 assert all(sha(fixture/n)==v for n,v in ctl['fixture_detached_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==3
 for a,b in [('notes/01-prefreeze-calculations.md','payload/math-note.md'),('code/finite_transport.py','payload/finite_transport.py'),('code/verify.py','payload/verify.py')]:assert (ROOT/a).read_bytes()==(fixture/b).read_bytes()
 cases=[];finite={}
 with tempfile.TemporaryDirectory(prefix='structural157-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-prefreeze-calculations.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data)
  q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong)
  q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_REPORT',False);q.write_bytes(data);check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'finite';sandbox.mkdir();(sandbox/'receipts').mkdir()
  for name,pattern,replacement,receipt in [('finite_bmp.py',r'^OUT=Path\([^\n]+\)$','OUT=Path('+repr(str(sandbox/'receipts/finite-bmp.json'))+')','finite-bmp.json'),('finite_transport.py',r"R=Path\('[^']+'\)",'R=Path('+repr(str(sandbox))+')','finite-transport.json')]:
   original=(ROOT/'code'/name).read_text();patched,count=re.subn(pattern,lambda _:replacement,original,count=1,flags=re.M);assert count==1
   program=sandbox/name;program.write_text(patched);r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=150,cwd=P);assert r.returncode==0,r.stderr
   result=read(sandbox/'receipts'/receipt);sealed=read(ROOT/'receipts'/receipt);result.pop('elapsed');sealed.pop('elapsed');assert result==sealed
   finite[name]={'only_fixed_output_and_second_saved_input_root_relocated':True,'original_sha256':sha(ROOT/'code'/name),'relocated_program_sha256':sha(program),'matches_sealed_receipt_except_elapsed':True,'result':result}
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest authenticates files/directories and bytes,not modes;parent snapshots exclude root-directory mode.'})
 dump('finite-replay.json',{'programs':finite,'limits':'Two disposable program copies;only fixed output destination and second saved-input root relocated;elapsed excluded from equality.48subsets/degrees0..5,256self-comparisons do not prove global invariance or all-degree results.'})
 dump('input-authentication.json',{'source_blobs':10,'source_bytes':sum(e['size'] for e in source),'primary_received_objects':5,'primary_archives':3,'independently_reconstructed_selected_members':4,'late_html_captures':2,'stable_whole_original_copies':8,'selected_excerpts':1,'selected_fixture_members':3,'limits':'Local byte/path/member authentication,no fresh protected source/primary/history semantic reading or PDF/render/transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':64,'whole_root_files':67,'subdirectories':14,'manifest_directories_including_dot':15,'source_blobs':10,'primary_received_objects':5,'primary_selected_members':4,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':8,'negative_cases':6,'finite_subsets':48,'finite_max_degree':5,'finite_nonfree_certificates':6,'finite_self_comparisons':256,'whole_actual_root_unchanged':True,'limits':'Byte integrity and exact finite observations only,no mathematical or contribution grade.'})
 print(json.dumps({'payload':64,'files':67,'subdirs':14,'source_blobs':10,'primary_objects':5,'primary_members':4,'stable_originals':8,'artifact_cases':8,'finite_subsets':48,'finite_self_comparisons':256}))
if __name__=='__main__':main()

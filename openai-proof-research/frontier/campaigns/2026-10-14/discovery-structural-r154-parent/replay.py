#!/usr/bin/env python3
"""Completed structural154 byte archive and bounded exact orbit diagnostic."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r154'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'a6670a07a7a0130b46c8254c592ca9621e75245d8449f2dfb74f76917548a97d','MANIFEST.json':'123385ddb057cad6ee6391677e71511beea53e5ec76eed19c05389e7158e79c6','REPORT.md':'badcd3a994bf068e2366406c70418d4e8b723995580e530be40b6762cd4d2312'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P);assert len(read(B/'tasks.json')['tasks'])==522
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':522,'task_index':518,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root excluding root-directory mode;not historical whole-project/OS provenance.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values());assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==66 and len(m['directories'])==21;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])-{'.'}
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'private/source-identities.json');companion=read(ROOT/'private/companion-identities.json');assert len(source)==13 and len(companion)==11
 prefixes=['preprints/An-FPRAS-for-Common-Integer-Polymatroid-Bases-with-Binary-Capacities-October-5-2026/','preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/'];cp='preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/'
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(q) for q in prefixes) and not p.endswith('.pdf')}
 assert len({e['canonical_path'] for e in companion})==11 and all(e['canonical_path'].startswith(cp) for e in companion)
 for e in source+companion:
  data=(ROOT/e['local']).read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 tr=read(ROOT/'private/tree-recheck.json');assert tr['entries']==13223 and not tr['truncated'] and tr['canonical_blobs_checked']==24 and tr['tree_sha256']==sha(tp)
 rec=read(ROOT/'private/primary/receipt.json');p=ROOT/'private/primary/chen-liu-v1.tar';assert p.stat().st_size==rec['bytes'] and sha(p)==rec['sha256'] and len(rec['members'])==2
 with tarfile.open(p,mode='r:*') as ar:
  for e in rec['members']:
   q=ROOT/e['path'];candidates=[n for n in ar.getnames() if n==q.name or n.endswith('/'+q.name)];assert len(candidates)==1 and ar.extractfile(candidates[0]).read()==q.read_bytes() and q.stat().st_size==e['size'] and sha(q)==e['sha256']
 rec=read(ROOT/'private/primary/branden-huh-receipt.json');p=ROOT/'private/primary/branden-huh-v8.tar';q=p.with_suffix('.tex');assert p.stat().st_size==rec['size'] and sha(p)==rec['sha256'] and gzip.decompress(p.read_bytes())==q.read_bytes() and q.stat().st_size==rec['text_size'] and sha(q)==rec['text_sha256']
 originals=read(ROOT/'private/incoming-original-identities.json');selected=read(ROOT/'private/selected-membership.json');assert len(originals)==len(selected)==11;stable=[];whole=0;excerpts=[]
 for e in originals:
  p=P/e['original_path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['size'],'sha256':e['sha256'],'limit':'Current whole-original byte identity;selected membership/read extents are separate.'})
 for e in selected:
  q=ROOT/e['local'];p=P/e['source_original'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
  if e['selection']=='whole file':assert p.read_bytes()==q.read_bytes();whole+=1
  else:
   lines=p.read_text().splitlines(keepends=True);body=''.join(lines[30:42]+lines[139:176]) if p.name=='i13-fresh-discovery.md' else ''.join(lines[90:110]);assert body.encode()==q.read_bytes();excerpts.append(e)
 assert whole==9 and len(excerpts)==2
 ctl=read(ROOT/'private/controls-receipt.json');fixture=ROOT/'seal/copied-controls';assert len(ctl['cases'])==8 and all(e['readonly_snapshot_equal'] and (e['returncode']==0)==e['expected_accept'] for e in ctl['cases'])
 for line in ctl['independent_sha256sum'].splitlines():digest,path=line.split(maxsplit=1);assert sha(fixture/Path(path).name)==digest
 fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==2 and (ROOT/'original/verify.py').read_bytes()==(fixture/'verify.py').read_bytes() and (ROOT/'notes/01-prefreeze-calculations.md').read_bytes()==(fixture/'note.md').read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural154-copy-',dir=O) as temp:
  copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'original/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);p=copy/'notes/01-prefreeze-calculations.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data);p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('empty_directory_extra',False);p.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);p=copy/'REPORT.md';data=p.read_bytes();p.write_bytes(data+b'x');check('changed_outside_report',False);p.write_bytes(data);check('restored',True);assert snap(copy)==before
  r=subprocess.run([sys.executable,'-I','-B',str(copy/'original/diagnostic.py')],cwd=temp,capture_output=True,text=True,timeout=60);assert r.returncode==0,(r.stdout,r.stderr);assert json.loads(r.stdout)==read(ROOT/'private/diagnostic.json');assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact evidence only;verifier binds exact files/directories,not modes.'})
 dump('finite-replay.json',{'script_sha256':sha(ROOT/'original/diagnostic.py'),'output_sha256':sha(ROOT/'private/diagnostic.json'),'output_exact_json_match':True,'cases':8,'labeled_states':1090,'orbit_records':120,'S_rate_comparisons':6300,'T_rates_separately_tested':False,'scope':'Bounded exact algebra,not binary-runtime/full-theorem/contribution evidence.'})
 dump('input-authentication.json',{'selected_source_blobs':24,'primary_incoming_sources':2,'independent_members':3,'stable_whole_original_byte_identities':11,'selected_whole_copies':9,'selected_excerpts':2,'selected_fixture_members':2,'limits':'Local byte/selection binding only;no fresh remote,protected-body semantic,PDF visual or transitive-proof attestation.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':66,'whole_root_files':69,'subdirectories':20,'source_blobs':24,'primary_incoming_sources':2,'independent_members':3,'stable_named_originals':stable,'selected_whole_copies':9,'selected_excerpts':excerpts,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'limits':'Artifact/bounded algebra archive,no independent grades.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':69,'payload':66,'subdirectories':20,'source_blobs':24,'primary_sources':2,'members':3,'stable_originals':11,'whole_copies':9,'excerpts':2,'artifact_cases':8,'S_rate_comparisons':6300}))
if __name__=='__main__':main()

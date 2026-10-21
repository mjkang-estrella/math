#!/usr/bin/env python3
"""Authenticate immutable T360S147 author packet;artifact/finite-algebra checks only."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r147'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b89f9d2bd1fef906abefd660cf3eb750585141773e78d2cbb3a12cf444652d8a','MANIFEST.json':'a16158d610590e192f20835d97a2186c06c8be38fe02c397809c3c628de44365','REPORT.md':'9b9dd65cce03cb54d01404b7f7dabc4df8ef2343aa12ea4bd9dd93f8763908bd'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':515,'task_index':512,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole root excluding root directory mode;not historical provenance/OS certificate.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
 assert all(sha(ROOT/n)==v for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert m['schema']=='exact-payload-v1' and m['excluded_envelopes']==list(ANCHORS) and len(m['files'])==76
 expected={e['path']:e for e in m['files']};assert len(expected)==76 and {p for p,e in before.items() if e['kind']=='file'}==set(expected)|set(ANCHORS)
 assert not any(e['kind'] not in ['file','directory'] for e in before.values())
 for n,e in expected.items():assert sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_size==e['size']
 freeze=read(ROOT/'FREEZE.json');assert freeze['path']=='STATEMENT.md' and freeze['size']==2121 and sha(ROOT/'STATEMENT.md')==freeze['sha256']=='5c36d8a2237f1416282ed5b930cc945ab78ec3fac42214685199c5228dc98ddc' and sha(ROOT/'CHECKPOINT.md')==freeze['prefreeze_checkpoint_sha256']
 assert sha(ROOT/'AUTHOR-PROOF.md')=='90f07fcca19ff034d9ac46d7dc94fefe85cf57aaf05ee814990b205d2ca0d719'
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'SOURCE-AUTH.json');assert source['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and len(source['files'])==17
 prefixes=['preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/','preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/']
 assert {e['canonical_path'] for e in source['files']}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(q) for q in prefixes) and not p.endswith('.pdf')}
 for e in source['files']:
  data=(ROOT/e['copy']).read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(ROOT/e['copy'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/'+source['pin']+'/'+e['canonical_path']
 primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==4;members=0
 for e in primary:
  data=(ROOT/e['incoming_path']).read_bytes();assert len(data)==e['size'] and sha(ROOT/e['incoming_path'])==e['sha256']
  if not e['selected']:continue
  try:
   ar=tarfile.open(fileobj=io.BytesIO(data),mode='r:*');get=lambda n:ar.extractfile(n).read()
  except tarfile.ReadError:
   body=gzip.decompress(data) if data.startswith(b'\x1f\x8b') else data;get=lambda n:body if n=='main.tex' else None
  for a in e['selected']:
   copy=(ROOT/a['copy']).read_bytes();assert copy==get(a['member']) and len(copy)==a['size'] and sha(ROOT/a['copy'])==a['sha256'];members+=1
 assert members==3
 stable=[];excerpts=[]
 for e in read(ROOT/'ORIGINALS-AUTH.json')['files']:
  q=ROOT/e['selected_copy'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
  if 'lines' in e:excerpts.append(e)
  else:
   p=P/e['original'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original'],'sha256':e['original_sha256'],'bytes':e['original_size']})
 assert len(stable)==13 and len(excerpts)==2
 auth=read(ROOT/'AUTH-CHECK.json');assert auth['source_bodies']==17 and auth['primary_incoming']==4 and auth['primary_selected_members']==3 and not auth['changed_originals_since_late_capture'] and len(auth['stable_originals_since_late_capture'])==15
 ctl=read(ROOT/'CONTROL-RESULTS.json');fixture=ROOT/'private/controls/fixture';assert len(ctl['controls'])==6 and all(e['accepted']==e['expected_accept'] and e['read_only_snapshot_match'] for e in ctl['controls'])
 assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items())
 fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==2
 for e in fm['files']:assert (ROOT/e['path']).read_bytes()==(fixture/e['path']).read_bytes() and sha(fixture/e['path'])==e['sha256'] and (fixture/e['path']).stat().st_size==e['size']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='t360s147-copy-',dir=O) as temp:
  copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);p=copy/'GAPS.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
  p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
  sandbox=Path(temp)/'finite';target=sandbox/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147';target.mkdir(parents=True);r=subprocess.run([sys.executable,'-I','-B',str(copy/'scratch/check_cofactors.py')],cwd=sandbox,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert (target/'DIAGNOSTIC.json').read_bytes()==(ROOT/'DIAGNOSTIC.json').read_bytes();assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'actual_root_unchanged':True,'limits':'Artifact cases;verifier does not bind directories,modes or hardlinks.'})
 dump('finite-replay.json',{'exact_matrix_cases':9,'hypothesis_order_diagnostics':3,'script_sha256':sha(ROOT/'scratch/check_cofactors.py'),'output_sha256':sha(ROOT/'DIAGNOSTIC.json'),'stdout':r.stdout,'output_exact_match':True,'actual_root_unchanged':True,'scope':'Finite Fraction algebra only;not PDE/Sobolev proof or contribution gate.'})
 dump('input-authentication.json',{'source_blobs':17,'primary_incoming':4,'selected_members':3,'byte_bound_extracts':1,'byte_bound_renders':2,'stable_whole_original_copies':13,'selected_excerpts':2,'limits':'Local canonical bytes/received archives and selected copies only;no fresh protected-body semantic,visual or remote identity reading.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':76,'whole_root_files':79,'subdirectories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':17,'primary_incoming':4,'primary_selected_members':3,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':6,'negative_cases':4,'finite_matrix_cases':9,'finite_hypothesis_diagnostics':3,'whole_actual_root_unchanged':True,'statement_sha256':freeze['sha256'],'proof_sha256':sha(ROOT/'AUTHOR-PROOF.md'),'limits':'Byte/finite algebra intake only,no independent correctness/contribution grade.Root mode excluded from snapshots;verifier omits modes,hardlinks,empty directories.'})
 print(json.dumps({'payload':76,'files':79,'source_blobs':17,'primary_objects':4,'selected_members':3,'stable_whole_copies':13,'excerpts':2,'artifact_cases':6,'finite_matrix_cases':9}))
if __name__=='__main__':main()

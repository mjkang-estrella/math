#!/usr/bin/env python3
"""Arithmetic121 byte archive and disposable artifact controls only."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r121'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d3cefbd2eeb1608a8e90a3f2c2c60e8828a67b8c8087ee71648e385d2d451fbb','MANIFEST.json':'4d77cf2aaaadd1f6c92d8218af05e08dd597a8183b5b1a372084efe6b7999a44','REPORT.md':'4925c598bd22198221f7072df8751bfc91717c30b2a8ed0e2d98f47b41b35113'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='023d83499311511044470b618fc94da4e13c0474' and len(read(B/'tasks.json')['tasks'])==526
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':526,'task_index':523,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']=='r121-packet-only-v1' and m['outside_envelopes']==list(ANCHORS) and len(m['files'])==78 and len(m['directories'])==11
 rows={e['path']:e for e in m['files']};assert len(rows)==78 and all(p.startswith('packet/') for p in rows)
 assert {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 meta=read(ROOT/'packet/private/tree-identity.json');tp=P/meta['path'];assert tp.stat().st_size==meta['size']==4858136 and sha(tp)==meta['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==meta['entries']==13223 and not tree['truncated'] and not meta['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'packet/private/source-identities.json');assert len(source)==18
 prefixes={e['canonical_path'].split('/')[1] for e in source};assert len(prefixes)==2
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.split('/')[1] in prefixes and p.endswith(('.tex','.bib'))}
 for e in source:
  q=P/e['copy'];assert q.is_relative_to(ROOT);data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'packet/private/primary-identities.json');assert len(primary)==8
 for e in primary:
  q=P/e['file'];t=P/e['text'];assert q.is_relative_to(ROOT) and t.is_relative_to(ROOT) and q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(t)==e['text_sha256']
 renders=[n for n in rows if n.startswith('packet/private/render/') and n.endswith('.png')];assert len(renders)==3
 incoming=read(ROOT/'packet/private/incoming-identities.json');assert len(incoming['records'])==12;stable=[];excerpts=[];whole=0
 for e in incoming['records']:
  p=P/e['incoming_original'];q=ROOT/e['copy'];assert q.stat().st_size==e['copy_size'] and sha(q)==e['copy_sha256']
  mutable=e['incoming_original']=='frontier/NEW-TEN-2026-10-14.md'
  if not mutable:
   assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['incoming_original'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  if e['selection']=='whole file':assert p.read_bytes()==q.read_bytes();whole+=1
  else:
   lines=p.read_text().splitlines(keepends=True);a,b=(1,100) if mutable else (529,550)
   assert ''.join(lines[a-1:b]).encode()==q.read_bytes()
   excerpts.append(e|{'whole_current_sha256':sha(p),'whole_capture_still_matches':sha(p)==e['original_sha256'],'limit':'Late selected excerpt,not initial or post-append whole-original stability.'})
 assert len(stable)==11 and whole==10 and len(excerpts)==2
 ctl=read(ROOT/'packet/private/controls/results.json');fixture=ROOT/'packet/private/controls/case'
 assert len(ctl['results'])==7 and all((e['exit_code']==0)==e['expected_accept'] and e['read_only'] for e in ctl['results'])
 assert all(sha(fixture/n)==v for n,v in ctl['own_fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==3
 for p,v in ctl['selected_original_hashes'].items():assert Path(p).is_relative_to(ROOT) and sha(Path(p))==v
 for a,b in [('packet/notes/feasibility.md','packet/feasibility.md'),('packet/code/verify.py','packet/verify.py'),('packet/private/source/section-08-global-sections.tex','packet/section-08-global-sections.tex')]:assert (ROOT/a).read_bytes()==(fixture/b).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic121-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'packet/notes/start.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'packet/private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  q=copy/'packet/private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only.Manifest binds bytes/membership/directories,not modes.Parent snapshots observe modes/links except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':18,'primary_pdfs':8,'text_derivatives':8,'bound_renders':renders,'stable_whole_original_byte_identities':11,'selected_whole_copies':10,'selected_excerpts':2,'selected_fixture_members':3,'limits':'Local bytes/paths/selected membership only;no fresh remote/protected-body semantic reading,extraction or PDF/render visual attestation.No published-final/transitive coverage added.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':78,'whole_root_files':81,'subdirectories':11,'source_blobs':18,'primary_pdfs':8,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical/formal/numerical suite or independent grade.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':81,'payload':78,'subdirectories':11,'source_blobs':18,'primary_pdfs':8,'stable_original_identities':11,'whole_copies':10,'excerpts':2,'artifact_cases':7}))
if __name__=='__main__':main()

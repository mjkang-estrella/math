#!/usr/bin/env python3
"""Read-only author-packet intake. No mathematical gate."""
import datetime, hashlib, json, os, stat, subprocess, sys, urllib.parse
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; ROOT=B/'fresh-analytic-discovery-r161'
ANCHORS={'FINAL.md':'4bfca9214a0e04560e65f73e0921ef7379f2c5e888cde8dbdaf991bd8b4314c6','MANIFEST.json':'889d99f950feed0a060f45456c1b78ddc9026065c034b6bf903cf31ae68ebc62','REPORT.md':'9c07eaa4b777b3f5009c02b5b569beef8997a4b4b91423a37182c0fd4d5a3a60'}
SCOPE='53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38'
PROOF='22d6114f858c90872c502560f6b814766aab096f65cc16b081ee01d107577e2f'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
 out={}
 def walk(d):
  for e in sorted(os.scandir(d),key=lambda e:e.name):
   p=Path(e.path); n=p.relative_to(root).as_posix(); st=p.lstat(); assert not e.is_symlink(),n
   if e.is_dir(follow_symlinks=False):out[n]={'kind':'directory','mode':stat.S_IMODE(st.st_mode)};walk(p)
   else:
    assert stat.S_ISREG(st.st_mode) and st.st_nlink==1,n
    out[n]={'kind':'file','mode':stat.S_IMODE(st.st_mode),'bytes':st.st_size,'sha256':sha(p),'nlink':st.st_nlink}
 walk(root);return out
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==562
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items());assert sha(ROOT/'FROZEN-STATEMENT.md')==SCOPE and sha(ROOT/'AUTHOR-PROOF.md')==PROOF
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==119 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==28
 for e in source:
  p=ROOT/'private/source'/e['path'];data=p.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(p)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'];assert urllib.parse.unquote(e['url'])=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path'] and e['url']==e['resolved_url']
 stable={};mutable=[];whole=spans=0
 for e in read(ROOT/'private/history/required-identities.json'):
  p=P/e['original_path'];q=ROOT/e['selected_path'];assert p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256'] and q.stat().st_size==e['selected_bytes'] and sha(q)==e['selected_sha256']
  if 'selected_start_byte' in e:assert q.read_bytes()==p.read_bytes()[e['selected_start_byte']:e['selected_end_byte_exclusive']];spans+=1
  else:assert p.read_bytes()==q.read_bytes();whole+=1
  target=mutable if e['original_path']=='frontier/NEW-TEN-2026-10-14.md' else None
  entry={'path':e['original_path'],'bytes':e['original_bytes'],'sha256':e['original_sha256']}
  if target is not None:target.append(entry)
  else:stable[e['original_path']]=entry
 selections=read(ROOT/'private/history/selected-identities.json');assert len(selections)==26
 for e in selections:
  p=P/e['original'];q=ROOT/e['selected'];assert p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256'] and q.stat().st_size==e['selected_bytes'] and sha(q)==e['selected_sha256'];assert q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[e['start_line']-1:e['end_line']]);stable[e['original']]={'path':e['original'],'bytes':e['original_bytes'],'sha256':e['original_sha256']}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)}
 primary=read(ROOT/'private/primary/identities.json');assert len(primary)==5
 for e in primary:
  p=ROOT/'private/primary'/(e['name']+'.pdf');q=p.with_suffix('.txt');assert p.read_bytes().startswith(b'%PDF') and p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and q.stat().st_size==e['text_bytes'] and sha(q)==e['text_sha256']
 renders=list((ROOT/'private/primary').glob('*.png'));assert len(renders)==1 and renders[0].read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 ctl=read(ROOT/'controls/results.json');assert len(ctl['results'])==3 and all(e['expected_exit']==e['actual_exit'] for e in ctl['results']);fixture=ROOT/'private/controls/baseline';fa=ctl['explicit_fixture_anchors'];assert all(sha(fixture/n)==v for n,v in fa.items());assert (fixture/'source-main.tex').read_bytes()==(ROOT/ctl['copied_source_original']).read_bytes() and (fixture/'statement.md').read_bytes()==(ROOT/'FROZEN-STATEMENT.md').read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,fa)]:
  state=snap(root);rm=stat.S_IMODE(root.stat().st_mode);args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),'--root',str(root)]
  for name,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,anchors[name]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==rm;runs.append({'root':'author packet' if root==ROOT else 'existing clean selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode})
 result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'frozen_scope_sha256':SCOPE,'author_proof_sha256':PROOF,'payload_files':119,'whole_root_files':122,'directories_excluding_root':sum(e['kind']=='directory' for e in before.values()),'source_blobs':28,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':5,'render_members':1,'required_whole_original_copies':whole,'required_selected_spans':spans,'exact_selected_history_sections':26,'stable_named_originals':list(stable.values()),'mutable_journal_identity_matched_before_append':mutable,'child_recorded_controls':3,'parent_read_only_replays':runs,'root_unchanged':True,'limits':'Artifact authentication only. No independent correctness/contribution grade, primary/visual/transitive proof reading, or new formal test. Verifier checks exact regular-file bytes/membership; parent additionally observes modes, directory membership, single links. Child reading/isolation limitations remain disclosed.'}
 dump('replay.json',result);print(json.dumps({k:result[k] for k in ['payload_files','whole_root_files','directories_excluding_root','source_blobs','primary_PDF_text_pairs','required_whole_original_copies','required_selected_spans','exact_selected_history_sections']}))
if __name__=='__main__':main()

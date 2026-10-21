#!/usr/bin/env python3
"""Analytic160 artifact authentication; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r160'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'7a8abc7c311795c7429f6aa27c664511b608ceaf8e1d5e001f996c31e6f3f5c6','MANIFEST.json':'f6948653ee7cbc9e7ad80917dc44bb45c682f8cc4369943b402091f77f70861b','REPORT.md':'3889b034f3bc654a419eaba3f75834942932517d696126e7e675536baaba1d7e'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==559
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==143 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:
  q=ROOT/e['path'];assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==64 and sum(e['size'] for e in source)==984656
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['canonical']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 stable={}
 for e in read(ROOT/'private/required-original-identities.json'):
  p=P/e['original'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and p.read_bytes()==(ROOT/e['copy']).read_bytes();stable[e['original']]={'path':e['original'],'bytes':e['size'],'sha256':e['sha256']}
 assert len(stable)==9
 ranges=read(ROOT/'private/history-selected-identities.json');assert len(ranges)==7
 for e in ranges:
  p=P/e['original'];q=ROOT/e['selected'];lo,hi=e['lines'];assert sha(p)==e['original_sha256'] and sha(q)==e['selected_sha256'];assert q.read_bytes()==b'\n'.join(p.read_bytes().splitlines()[lo-1:hi])+b'\n';stable[e['original']]={'path':e['original'],'bytes':p.stat().st_size,'sha256':e['original_sha256']}
 rules=[]
 for e in read(ROOT/'private/rule-section-identities.json'):
  p=P/e['original'];q=ROOT/e['selected_copy'];lo,hi=e['lines'];assert q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[lo-1:hi]) and sha(q)==e['selected_sha256'];matched=p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256_at_late_identity_check'];rules.append({'path':e['original'],'whole_late_identity_matches_at_intake':matched,'selected_range_matches':True,'recorded_whole_sha256':e['original_sha256_at_late_identity_check'],'observed_whole_sha256':sha(p),'limits':'Late byte identity only,not first-read stability. Journal will receive an authorized parent append.' if e['original'].startswith('frontier/') else 'Late byte identity only,not first-read stability.'})
  if e['original']=='sources/CONTENTS.md':assert matched;stable[e['original']]={'path':e['original'],'bytes':p.stat().st_size,'sha256':sha(p)}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':(P/'sources/preprints-tree.json').stat().st_size,'sha256':sha(P/'sources/preprints-tree.json')};assert len(stable)==12
 primary=read(ROOT/'private/primary/identities.json');assert len(primary)==6
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(ROOT/'private/primary'/(e['name']+'.txt'))==e['text_sha256']
 renders=list((ROOT/'private/primary').rglob('*.png'));assert len(renders)==5 and all(q.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for q in renders)
 ctl=read(ROOT/'private/copied-control-results.json');assert len(ctl['outcomes'])==4 and all(e['expected_exit']==e['actual_exit'] for e in ctl['outcomes']);fixture=ROOT/'private/controls/clean'
 for e in ctl['selected_originals']:assert (ROOT/e['source']).read_bytes()==(fixture/e['member']).read_bytes() and sha(ROOT/e['source'])==e['sha256']
 cert=read(ROOT/'notes/shell-cone-certificate.json');assert cert['rank']==21 and len(cert['rotations'])==60 and len(cert['columns'])==60 and len(cert['basis'])==21 and cert['uniform_column_sum_zero']
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['outcomes'][0]['anchors'])]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),'--root',str(root),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],'--report-sha',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing clean selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':143,'whole_root_files':146,'source_blobs':64,'source_bytes':984656,'primary_PDF_text_pairs':6,'render_members':5,'stable_named_originals':list(stable.values()),'whole_required_original_copies':9,'exact_selected_I80_ranges':7,'late_rule_section_checks':rules,'child_recorded_artifact_cases':4,'parent_read_only_replays':runs,'recorded_finite_harmonic_dimension':21,'recorded_finite_rotation_columns':60,'finite_certificate_not_rerun_or_independently_graded':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate or fresh primary/visual proof reading. Manifest binds exact regular-file bytes/membership,not empty directories,modes or links. Parent separately observed full tree/modes and checked actual single links. Selected journal bytes persist; whole mutable journal is not a stable named input after parent append.'})
 print(json.dumps({'payload':143,'files':146,'source_blobs':64,'primary_pairs':6,'renders':5,'stable_originals':12,'read_only_replays':2,'late_rule_checks':rules}))
if __name__=='__main__':main()

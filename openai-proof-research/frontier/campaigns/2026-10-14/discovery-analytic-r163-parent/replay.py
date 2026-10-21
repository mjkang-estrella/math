#!/usr/bin/env python3
"""Read-only Analytic163 no-nominee artifact archive; private manifest stays local."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r163';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'697ae7591b50db5e1f61d61db0768d982affe318e6b5de6975a1dc4ab8d4145b','private/MANIFEST.json':'4dcf461b7e25b0fe8c39d8ac6d55950f710ecc0acf5926ca2ba7692c168c8582','REPORT.md':'7bc378d4f5287bbe58538848a2bf4796785ce74bbcaf381917eaae7117eee5ed'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==573
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items());assert read(ROOT/'ANCHORS.json')==ANCHORS
 m=read(X/'MANIFEST.json');assert len(m['files'])==68 and m['schema']=='r163-exact-selected-packet-v1';actual={n for n,e in before.items()if e['kind']=='file' and not n.startswith('private/controls/')};assert actual=={e['path']for e in m['files']}|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=[json.loads(v)for v in (X/'objects.jsonl').read_text().splitlines()];assert len(source)==15
 for e in source:
  q=P/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=[json.loads(v)for v in (X/'primary/versions.jsonl').read_text().splitlines()];assert len(primary)==5
 for e in primary:
  q=X/'primary'/(e['name']+('.pdf'if 'pdf'in e.get('content_type','')or e['name']in ['BGP-2004','DL-1989']else '.html'));assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.with_suffix('.txt').is_file()
 for p in (X/'render').glob('*.png'):assert p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 selected=read(X/'selected-originals/selections.json');assert len(selected)==13;stable={}
 for e in selected:
  p=P/e['path'];q=ROOT/e['selected_copy'];assert q.read_bytes()==p.read_bytes()[e['start']:e['end']] and sha(q)==e['selection_sha256'] and oct(stat.S_IMODE(p.stat().st_mode))==e['original_mode']
  if e['path']=='frontier/NEW-TEN-2026-10-14.md':assert hashlib.sha256(p.read_bytes()[:e['total']]).hexdigest()==e['sha256']
  else:assert p.stat().st_size==e['total'] and sha(p)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)}
 def verify(root):
  args=[sys.executable,'-I','-B',str(X/'verify_packet.py'),str(root),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['private/MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']];r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip()}
 actual_replay=verify(ROOT);control=verify(X/'controls/clean');assert (X/'controls/clean/CALCULATIONS.md').read_bytes()==(ROOT/'CALCULATIONS.md').read_bytes();results=read(X/'controls/results.json');assert results['originals_unchanged'] and len(results['checks'])==6 and all(e['actual_exit']==e['expected_exit']for e in results['checks'])
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 total=sum(e['kind']=='file'for e in before.values());dirs=1+sum(e['kind']=='dir'for e in before.values());dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'selected_manifest_files':68,'selected_files_with_three_exclusions':71,'whole_root_files_including_controls':total,'whole_directories_including_root':dirs,'source_objects':15,'source_bytes':sum(e['bytes']for e in source),'primary_raw_text_pairs':5,'primary_PDF_text_pairs':3,'primary_HTML_text_pairs':2,'render_members':6,'selected_original_copies':13,'stable_named_originals':list(stable.values()),'actual_read_only_replay':actual_replay,'existing_intact_copy_replay':control,'artifact_control_outcomes_recorded':6,'root_unchanged':True,'limits':'Artifact authentication only. Parent read complete original mathematical notebooks,FINAL/REPORT and private comparison,extents,reading/isolation/seal accounts/verifier. Protected source/primary/visual proof bodies not semantically read by parent. Manifest excludes controls and does not bind directory census; parent additionally observes whole-root modes,links and directories. Private manifest/reading/identity inventory,replay,navigation remain local unstaged. No mathematical gate.'});print(json.dumps({'selected_payload':68,'whole_root_files':total,'source_objects':15,'primary_raw_text_pairs':5,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()

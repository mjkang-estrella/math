#!/usr/bin/env python3
"""Read-only Arithmetic134 no-nominee artifact archive."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r134';PAY=ROOT/'payload';X=PAY/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'5a9f9c17868970a70700eaaac47eb082553d5da6ea50da221c497f7fbdd2d5cb','MANIFEST.json':'c843083229f7893533a6fc74050d936b13021edde644c4979a04750756b77bbb','REPORT.md':'8ca70533a889d2b710062e36125c4de09cba44bd973eb269ea7c0bcb3ac71fbc'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==568
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==72 and len(m['directories'])==8 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source-authentication.json');assert len(source)==16
 for e in source:
  q=PAY/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable=[]
 for e in read(X/'completed-read-extents.json'):
  p=P/e['project_path'];q=PAY/e['local'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and e['read']==[0,e['bytes']];stable.append({'path':e['project_path'],'bytes':e['bytes'],'sha256':e['sha256']})
 assert len(stable)==7;e=read(X/'history-selection.json');p=P/e['path'];assert sha(p)==e['sha256'] and (X/'history-i145-section.md').read_bytes()==p.read_bytes()[e['start']:e['end']];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':e['sha256']})
 e=read(X/'contents-selection.json');p=P/e['path'];assert (X/'contents069.txt').read_bytes()==p.read_bytes()[e['start_byte']:e['end_byte_exclusive']];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)});stable.append({'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)})
 assert (X/'acceptance.txt').read_bytes()==(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()[4801:6347]
 primary=read(X/'primary/acquisition.json');assert len(primary)==7
 for e in primary:
  q=X/'primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 assert (X/'primary/af-p14.png').read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 clean=PAY/'controls/clean';altered=PAY/'controls/altered';control=read(clean/'CONTROL.json');assert (clean/'selection.md').read_bytes()==(PAY/'notes/central-descent-calculation.md').read_bytes() and (clean/'CONTROL.json').read_bytes()==(altered/'CONTROL.json').read_bytes() and len((clean/'selection.md').read_bytes())==len((altered/'selection.md').read_bytes()) and sum(a!=b for a,b in zip((clean/'selection.md').read_bytes(),(altered/'selection.md').read_bytes()))==1
 args=[sys.executable,'-I','-B',str(PAY/'verify_packet.py'),str(ROOT)]
 for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,ANCHORS[n]])
 r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr)
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':72,'whole_root_files':75,'directories_excluding_root':8,'source_objects':16,'source_bytes':sum(e['bytes'] for e in source),'primary_PDF_text_pairs':7,'render_members':1,'whole_completed_original_copies':7,'exact_historical_byte_sections':1,'stable_named_originals':stable,'child_Laurent_identities_recorded':6,'copied_control_cases':2,'actual_read_only_replay':{'returncode':r.returncode,'stdout':r.stdout.strip(),'unchanged':True},'clean_control_matches_current_note':True,'altered_control_one_byte_difference':True,'root_unchanged':True,'limits':'Artifact authentication only. Parent read all original public notes/code and private reading account, not protected source/primary/visual proof bodies. Finite Laurent script not rerun. Verifier binds membership/bytes; parent additionally observes modes and single links. Protected identities/replay and reading account remain local unstaged.'});print(json.dumps({'payload':72,'files':75,'source_objects':16,'primary_pairs':7,'stable_named_originals':10,'read_only_replays':1,'integrated_copied_controls':2}))
if __name__=='__main__':main()

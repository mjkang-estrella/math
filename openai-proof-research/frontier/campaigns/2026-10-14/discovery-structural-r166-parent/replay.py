#!/usr/bin/env python3
"""Structural166 authenticated intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r166'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d550e9a050e4a2e89e2df85a0f69d3906b9c8824c15264352edcdc436524aee2','MANIFEST.json':'dde6ef92ca895cddc6ee6a40cb08ebdd1c90fc296127783e81fbb50469337735','REPORT.md':'b151082eff1b1ea858e9dedca7956227934b0384f07056a849ac42c4dcfe2721'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==560
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==64 and len(m['directories'])==33 and rm==m['directories']['.'];assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256'] and stat.S_IMODE((ROOT/n).stat().st_mode)==e['mode'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-authentication.json');assert len(source)==10
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable={}
 for e in read(ROOT/'private/incoming-originals.json'):
  p=P/e['path'];q=ROOT/'private/completed-originals'/e['path'].removeprefix(str(B.relative_to(P))+'/');assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and p.read_bytes()==q.read_bytes();stable[e['path']]={'path':e['path'],'bytes':e['size'],'sha256':e['sha256']}
 assert len(stable)==11
 for e in read(ROOT/'private/history-selected-identities.json'):
  p=P/e['original'];q=ROOT/e['selected_path'];assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and sha(q)==e['selected_sha256'];data=p.read_bytes()
  if e['extent']=='full':body=data
  else:lo,hi=(25,32) if 'r118/' in e['original'] else (17,32);body=b''.join(data.splitlines(keepends=True)[lo-1:hi])
  assert q.read_bytes()==body;stable[e['original']]={'path':e['original'],'bytes':e['original_size'],'sha256':e['original_sha256']}
 for e in read(ROOT/'private/late-original-identities.json'):
  p=P/e['original'];q=ROOT/e['selected'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and sha(q)==e['selected_sha256'] and q.read_bytes()==(p.read_bytes() if e['extent']=='full' else p.read_bytes()[1407:1975]);stable[e['original']]={'path':e['original'],'bytes':e['size'],'sha256':e['sha256']}
 assert len(stable)==16
 for n,copy in [('AGENTS.md','AGENTS.md'),('sources/upstream.json','sources/upstream.json')]:assert (ROOT/'private/project-inputs'/copy).read_bytes()==(P/n).read_bytes();stable[n]={'path':n,'bytes':(P/n).stat().st_size,'sha256':sha(P/n)}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':(P/'sources/preprints-tree.json').stat().st_size,'sha256':sha(P/'sources/preprints-tree.json')};assert (ROOT/'private/project-inputs/acceptance-section.md').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes() and (ROOT/'private/source185-catalogue-block.md').read_bytes() in (P/'sources/CONTENTS.md').read_bytes()
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==4
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(q.with_suffix('.txt'))==e['text_sha256']
 renders=list((ROOT/'private/primary').rglob('*.png'));assert len(renders)==2 and all(q.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for q in renders)
 ctl=read(ROOT/'private/controls/outcomes.json');assert len(ctl['controls'])==8 and all(e['expected_accept']==e['observed_accept'] and e['unchanged_by_verifier'] for e in ctl['controls']);fixture=ROOT/'private/controls/fixture';assert (fixture/'artifact/verify.py').read_bytes()==(ROOT/'artifact/verify.py').read_bytes() and (fixture/'private/source-wrapper.tex').read_bytes()==(ROOT/'private/source185/paper.tex').read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['fixture_anchors'])]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'artifact/verify.py'),str(root),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':64,'whole_root_files':67,'directories_including_root':33,'source_blobs':10,'primary_PDF_text_pairs':4,'render_members':2,'stable_named_originals':list(stable.values()),'incoming_history_identity_records':17,'unique_history_originals':16,'mandatory_whole_copies':11,'additional_whole_copies':3,'selected_history_excerpts':3,'child_recorded_artifact_cases':8,'parent_read_only_replays':runs,'fixture_calculation_equals_final_not_asserted':True,'fixture_calculation_predates_final_explanation_as_disclosed':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate or fresh primary/visual proof reading. Manifest/verifier bind exact files/directories,modes,bytes and single links. Fixture has its own anchored inventory; historical snapshot equivalence to final math is not asserted.'});print(json.dumps({'payload':64,'files':67,'source_blobs':10,'primary_pairs':4,'renders':2,'stable_originals':19,'read_only_replays':2}))
if __name__=='__main__':main()

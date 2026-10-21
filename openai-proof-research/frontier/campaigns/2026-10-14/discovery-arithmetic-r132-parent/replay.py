#!/usr/bin/env python3
"""Arithmetic132 authenticated archive; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r132'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'envelopes/FINAL.md':'432335af118869eb6bbc16293b3cffb4c34af2c641c3bb2683b46c7492ac087c','envelopes/MANIFEST.json':'24e210018a2af894dce90493ff6c367635932da547594e24e1b3b305f6bf2a06','envelopes/REPORT.md':'ca5d2763bf368edf4d4c73f53c06ad89163c8d9ec304dcc77a816a3ddc039486'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==561
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'envelopes/MANIFEST.json');assert len(m['files'])==72 and len(m['directories'])==13;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'artifacts/source-authentication.json');assert len(source)==13
 for e in source:
  q=P/e['local'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable=[];whole=selected=rules=0
 for e in read(ROOT/'artifacts/incoming-identities.json'):
  p=P/e['incoming_original'];q=ROOT/e['selected_copy']
  if 'size' not in e:assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256'] and q.read_bytes() in p.read_bytes();rules+=1;continue
  assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['incoming_original'],'bytes':e['size'],'sha256':e['sha256']})
  if e['extent']=='whole named/direct original':assert p.read_bytes()==q.read_bytes();whole+=1
  else:
   lo,hi=(178,190) if 'i136-' in e['incoming_original'] else (46,61);assert q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[lo-1:hi]) and sha(q)==e['selected_sha256'];selected+=1
 assert len(stable)==13 and whole==11 and selected==2 and rules==2;stable.append({'path':'sources/preprints-tree.json','bytes':(P/'sources/preprints-tree.json').stat().st_size,'sha256':sha(P/'sources/preprints-tree.json')})
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==7
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(ROOT/'private/primary'/(e['name']+'.txt'))==e['text_sha256']
 renders=list((ROOT/'private/primary').rglob('*.png'));assert len(renders)==2 and all(q.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for q in renders)
 ctl=read(ROOT/'artifacts/copied-controls.json');assert len(ctl['cases'])==6 and all(e['expected_accept']==(e['returncode']==0) for e in ctl['cases']);fixture=ROOT/'private/copied-controls';fa={n:m['files']['private/copied-controls/'+n]['sha256'] for n in ANCHORS};diag=read(ROOT/'artifacts/exact-calculations.json');assert len(diag['triangular_integral_checks'])==12 and sum(len(e['finite_counts']) for e in diag['triangular_integral_checks'])==24
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,fa)]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify.py'),str(root),'--final',anchors['envelopes/FINAL.md'],'--manifest',anchors['envelopes/MANIFEST.json'],'--report',anchors['envelopes/REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing selected fixture with anchors bound by actual manifest','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':72,'whole_root_files':75,'directories_excluding_root':13,'source_blobs':13,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':7,'primary_locator_only_version':1,'render_members':2,'stable_named_originals':stable,'whole_original_copies':11,'exact_selected_history_excerpts':2,'selected_rule_sections':2,'child_recorded_artifact_cases':6,'parent_read_only_replays':runs,'finite_integral_identities_recorded':12,'bounded_lattice_counts_recorded':24,'finite_diagnostics_not_rerun':True,'fixture_sample_original_equivalence_not_independently_asserted':True,'fixture_anchors_bound_by_actual_payload_manifest':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate or fresh primary/visual proof reading. Manifest binds exact regular files/directories and bytes; verifier checks single links,not modes/timestamps. Parent separately observed full tree/modes. Old excluded screen037 scope remains uncleared.'});print(json.dumps({'payload':72,'files':75,'source_blobs':13,'primary_pairs':7,'renders':2,'stable_originals':14,'read_only_replays':2}))
if __name__=='__main__':main()

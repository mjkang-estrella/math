#!/usr/bin/env python3
"""Authenticate Arithmetic130; replay existing controls without creating a suite."""
import datetime,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r130'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'envelopes/FINAL.md':'af5261f8153bb9ecf37d292b8909cf7d75d3bf3cf9678091061904d574b4626d','envelopes/MANIFEST.json':'f99d059a45a44269fdee1f4b09616d77a5ebfe7c59ed1a5712d8868155a09614','envelopes/REPORT.md':'4793ad647b2cb4bcb4117e5f69c95b262f8011d5292868d7c2a4d14364bddf57'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==554
 before=snap(ROOT);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'envelopes/MANIFEST.json');assert len(m['files'])==100 and len(m['directories'])==30 and {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==6
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable=[]
 for e in read(ROOT/'private/history/incoming-original-identities.json'):
  p=P/e['original_path'];q=ROOT/e['copy_member'];assert p.stat().st_size==q.stat().st_size==e['original_bytes'] and sha(p)==sha(q)==e['original_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_bytes'],'sha256':e['original_sha256']})
 assert len(stable)==16
 for e in read(ROOT/'private/history/selected-original-identities.json'):assert (P/e['original']).stat().st_size==(ROOT/e['copy']).stat().st_size==e['size'] and sha(P/e['original'])==sha(ROOT/e['copy'])==e['sha256']
 assert (ROOT/'private/navigation/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==3
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file()
 for name,filename in [('transitive-acquisition.json','mignotte-waldschmidt1978.pdf'),('waldschmidt-acquisition.json','waldschmidt1980.pdf')]:
  e=read(ROOT/'private/primary'/name);q=ROOT/'private/primary'/filename;assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file()
 assert len(list((ROOT/'private/primary').glob('*.png')))==11
 ctl=read(ROOT/'controls/results.json');assert len(ctl['controls'])==6 and all((e['returncode']==0)==e['expected_valid'] for e in ctl['controls']) and ctl['baseline_bytes_unchanged'];fixture=ROOT/'controls/baseline';assert sha(fixture/'notes/reduction-boundary.md')==sha(ROOT/'notes/reduction-boundary.md') and sha(fixture/'tools/verify.py')==sha(ROOT/'tools/verify.py');inner={n:sha(fixture/n) for n in ANCHORS}
 runs=[]
 def verify(root,anchors,want,label):
  state=snap(root);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'tools/verify.py'),str(root),'--final-sha',anchors['envelopes/FINAL.md'],'--manifest-sha',anchors['envelopes/MANIFEST.json'],'--report-sha',anchors['envelopes/REPORT.md']],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(root)==state;runs.append({'root':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
 verify(ROOT,ANCHORS,True,'actual packet')
 for e in ctl['controls']:
  anchors=inner.copy()
  if e['fixture']=='wrong-anchor':anchors['envelopes/FINAL.md']='0'*64
  verify(ROOT/'controls'/e['fixture'],anchors,e['expected_valid'],e['fixture'])
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':100,'whole_root_files':103,'subdirectories':30,'source_blobs':6,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':5,'render_members':11,'stable_named_originals':stable,'whole_original_copies':16,'child_recorded_artifact_cases':6,'parent_read_only_replays':runs,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact authentication only; two scanned primary text extractions are incomplete and child image-reading limits remain. No fresh primary/visual proof reading,independent mathematical gate or formal suite. Manifest binds content/membership/single links,not modes/timestamps.'})
 print(json.dumps({'payload':100,'files':103,'dirs':30,'source_blobs':6,'primary_pairs':5,'renders':11,'stable_originals':16,'read_only_replays':7}))
if __name__=='__main__':main()

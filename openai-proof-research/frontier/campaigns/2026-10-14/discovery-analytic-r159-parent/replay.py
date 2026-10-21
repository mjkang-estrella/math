#!/usr/bin/env python3
"""Analytic159 authentication and existing read-only fixture replay; no math gate."""
import datetime,gzip,hashlib,importlib.util,io,json,stat,subprocess,sys,tarfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r159'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d86603ddf653030399db3529b13b7e5a789703d5379dde1932a4ca27651d27da','MANIFEST.json':'2f86cdd753e78c36188bd83d38a3db90b4d4927be255d18762e031ddf2925d38','REPORT.md':'db35355a1f3e340134f56be4336919ab4f7880bd336887cf1b516f9de079d2b4'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==556
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==99 and sum(e['bytes'] for e in m['files'])==1114820;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:
  q=ROOT/e['path'];assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json')+read(ROOT/'private/source/mixing-authentication.json');assert len(source)==47
 for e in source:
  q=P/e['local'];data=q.read_bytes();node=entries[e['canonical']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 stable={}
 for e in read(ROOT/'private/history/required-identities.json'):
  p=P/e['original'];q=P/e['selected'];assert p.stat().st_size==e['incoming_bytes'] and sha(p)==e['incoming_sha256']==e['selected_sha256'] and p.read_bytes()==q.read_bytes();stable[e['original']]={'path':e['original'],'bytes':p.stat().st_size,'sha256':sha(p)}
 assert len(stable)==7
 for rel,n in [('AGENTS.md','AGENTS.md'),('sources/upstream.json','upstream.json')]:
  p=P/rel;assert (ROOT/'private/history'/n).read_bytes()==p.read_bytes();stable[rel]={'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)}
 ranges=read(ROOT/'private/history/selected-identities.json');assert len(ranges)==8
 for e in ranges:
  p=P/e['original'];q=P/e['selected'];assert p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256'] and sha(q)==e['selected_sha256'];assert q.read_bytes()==b'\n'.join(p.read_bytes().splitlines()[e['start']-1:e['end']])+b'\n';stable[e['original']]={'path':e['original'],'bytes':e['original_bytes'],'sha256':e['original_sha256']}
 assert len(stable)==12 and (ROOT/'private/history/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary/authentication.json');x=read(ROOT/'private/primary/xiao-authentication.json');x['name']='xiao-v2';primary.append(x);assert len(primary)==3
 for e in primary:
  incoming=ROOT/'private/primary'/(e['name']+'.incoming');data=incoming.read_bytes();assert len(data)==e['bytes'] and sha(incoming)==e['sha256']
  for member in e['selected']:
   if member['member']=='single-source':body=gzip.decompress(data);q=ROOT/'private/primary'/(e['name']+'.tex')
   else:
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as tf:body=tf.extractfile(member['member']).read()
    q=ROOT/'private/primary'/e['name']/member['member']
   assert q.read_bytes()==body and len(body)==member['bytes'] and sha(q)==member['sha256']
 ctl=read(ROOT/'private/controls/results.json');assert len(ctl['results'])==5 and all((e['exit']==0)==(n in ['clean','restored']) for n,e in ctl['results'].items());fixture=ROOT/'private/controls/selected-copy'
 for e in ctl['copied_originals']:assert sha(P/e['original'])==e['original_sha256']==sha(fixture/e['selected'])==e['selected_sha256']
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['anchors'])]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify.py'),'--root',str(root),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':99,'payload_bytes':1114820,'whole_root_files':102,'source_blobs':47,'source_bytes':sum(e['bytes'] for e in source),'primary_incoming_containers':3,'selected_primary_members':3,'stable_named_originals':list(stable.values()),'required_completed_whole_copies':7,'rule_whole_copies':2,'exact_selected_history_ranges':8,'child_recorded_artifact_cases':5,'parent_read_only_replays':runs,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no independent mathematical gate or fresh primary/visual proof reading. Manifest binds exact regular-file bytes/membership,not directories,modes or hardlinks. Parent separately observed full tree/modes and checked actual single links.'})
 print(json.dumps({'payload':99,'files':102,'source_blobs':47,'primary_containers':3,'selected_primary_members':3,'stable_originals':12,'read_only_replays':2}))
if __name__=='__main__':main()

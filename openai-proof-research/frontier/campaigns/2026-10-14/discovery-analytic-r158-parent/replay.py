#!/usr/bin/env python3
"""Proportionate Analytic158 intake: authenticate and replay existing verifiers."""
import datetime,gzip,hashlib,importlib.util,io,json,subprocess,sys,tarfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r158'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'8aac2053c6325c018b3fc8d8fa97f3995610be4d6c97089ac1b52d7364ff4dc9','MANIFEST.json':'509e50d8e7ce852b0ca35e59867f2915ba918b8dbdb06af45cfdb8e84e10364c','REPORT.md':'e3c2196f4185e8fb61aff6d48e9e4e5755b0c852af60d2df6406fcbdaf64d0c4'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==553
 before=snap(ROOT);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==90 and {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-auth.json');assert len(source)==27 and sum(e['size'] for e in source)==1011495
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable={}
 for e in read(ROOT/'private/required-identities.json'):
  p=P/e['path'];q=ROOT/e['copy'];assert p.stat().st_size==e['size']==q.stat().st_size and sha(p)==e['sha256']==sha(q);stable[e['path']]=e
 for name in ['history-r154-identities.json','history-r157-identities.json']:
  for e in read(ROOT/'private'/name):
   p=P/e['path'];q=ROOT/'private/history'/e['path'].removeprefix(str(B.relative_to(P))+'/').replace('/','__');assert p.stat().st_size==q.stat().st_size==e['size'] and sha(p)==sha(q)==e['sha256'];stable[e['path']]=e
 assert len(stable)==16
 for e in read(ROOT/'private/history-selected-auth.json'):
  p=P/e['original'];q=ROOT/e['selection'];a,b=e['lines'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256']==hashlib.sha256(p.read_bytes()).hexdigest() and sha(q)==e['selected_sha256'] and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b]);stable[e['original']]={'path':e['original'],'size':e['size'],'sha256':e['sha256']}
 assert len(stable)==18 and (ROOT/'private/acceptance.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary/auth.json');assert len(primary)==4 and sum(len(e['selected']) for e in primary)==5
 for e in primary:
  folder=ROOT/'private/primary'/e['id'];q=folder/'incoming';assert q.stat().st_size==e['incoming']['size'] and sha(q)==e['incoming']['sha256']
  if e['selected'][0]['member']=='single source':assert len(e['selected'])==1 and gzip.decompress(q.read_bytes())==(folder/e['selected'][0]['copy']).read_bytes()
  else:
   with tarfile.open(fileobj=io.BytesIO(q.read_bytes()),mode='r:*') as tar:
    for s in e['selected']:assert tar.extractfile(s['member']).read()==(folder/s['copy']).read_bytes()
  for s in e['selected']:assert (folder/s['copy']).stat().st_size==s['size'] and sha(folder/s['copy'])==s['sha256']
 ctl=read(ROOT/'private/controls/results.json');assert len(ctl['results'])==7 and all(e['expected_accept']==e['actual_accept'] for e in ctl['results']);fixture=ROOT/'private/controls/selected-copy'
 for e in ctl['selected_originals']:assert (ROOT/e['original']).stat().st_size==(fixture/e['copy']).stat().st_size==e['size'] and sha(ROOT/e['original'])==sha(fixture/e['copy'])==e['sha256']
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['anchors'])]:
  state=snap(root);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'tools/verify.py'),str(root),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state;runs.append({'root':'actual packet' if root==ROOT else 'existing selected-copy fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':90,'whole_root_files':93,'subdirectories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':27,'source_bytes':1011495,'primary_incoming_objects':4,'primary_selected_members':5,'required_completed_whole_copies':14,'required_instruction_whole_copies':2,'history_exact_ranges':5,'history_unique_whole_originals':2,'stable_named_originals':list(stable.values()),'child_recorded_artifact_cases':7,'parent_read_only_replays':runs,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; no independent correctness/contribution grade,fresh primary-body reading or finite/formal suite. Manifest binds bytes/file membership,not empty directories,modes or hardlink count.'})
 print(json.dumps({'payload':90,'files':93,'source_blobs':27,'primary_objects':4,'primary_members':5,'stable_originals':18,'read_only_replays':2}))
if __name__=='__main__':main()

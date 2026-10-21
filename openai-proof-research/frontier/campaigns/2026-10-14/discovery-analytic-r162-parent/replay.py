#!/usr/bin/env python3
"""Read-only artifact intake for Analytic162; no mathematical gate."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r162';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'33126ba7dc04734feab8464a47c6162edb4d30ad2b19e82acece6f7da6e584f5','MANIFEST.json':'72f9242333e77f08dc5143cfa236a793193373391f87ef836623c681f6ab9c56','REPORT.md':'a3c09c34b5cc9bb5487aff96fe695733e96982211edc631b752307ad8f987fed'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==569
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==96 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source-identities.json');assert len(source)==47
 for e in source:
  q=P/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(X/'primary/versions.json')+[read(X/'primary'/n)for n in ['2011.15090v1-identity.json','dm-publisher-identity.json','2007.14707v1-identity.json','1006.3028v2.identity.json']];assert len(primary)==8
 for e in primary:
  name=e.get('id','1006.3028v2');q=X/'primary'/(name+'.html');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'];assert q.with_suffix('.txt').is_file()
 stable={};rows=[json.loads(v)for v in (X/'read-extents.jsonl').read_text().splitlines()]
 for e in rows:
  p=P/e['path'];p=p if p.exists() else ROOT/e['path'];assert p.is_file() and 0<=e['start']<=e['end']<=e['total']
  if e['path']=='frontier/NEW-TEN-2026-10-14.md':assert hashlib.sha256(p.read_bytes()[:e['total']]).hexdigest()==e['sha256']
  else:assert p.stat().st_size==e['total'] and sha(p)==e['sha256']
  if not p.is_relative_to(ROOT) and e['path']!='frontier/NEW-TEN-2026-10-14.md':stable[e['path']]={'path':e['path'],'bytes':e['total'],'sha256':e['sha256']}
 for e in read(X/'authentication-check.json')['exact_instruction_identities']:
  p=P/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':e['bytes'],'sha256':e['sha256']}
 def verify(root,anchors):
  args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),'--root',str(root)]
  for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip()}
 actual=verify(ROOT,ANCHORS);good=X/'copied-controls/good';clean=verify(good,{n:sha(good/n)for n in ANCHORS});assert (good/'copied-calculations.md').read_bytes()==(ROOT/'CALCULATIONS.md').read_bytes();assert len(read(X/'copied-controls/control-results.json')['results'])==3
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':96,'whole_root_files':99,'directories_excluding_root':len(m['directories']),'source_objects':47,'source_bytes':sum(e['size']for e in source),'primary_HTML_text_pairs':8,'read_extent_events':len(rows),'stable_named_originals':list(stable.values()),'actual_read_only_replay':actual,'existing_clean_fixture_replay':clean,'copied_control_cases_recorded':3,'root_unchanged':True,'limits':'Artifact authentication only. Parent read all original public notes/verifier and private comparison,extents,reading/isolation accounts. Parent did not read protected source/primary mathematical bodies. No finite mathematical test or independent gate. Full observed root,protected identity replay/navigation stay local unstaged.'});print(json.dumps({'payload':96,'files':99,'sources':47,'primary_pairs':8,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()

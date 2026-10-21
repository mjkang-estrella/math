#!/usr/bin/env python3
"""Artifact-only adoption of unsuccessful Structural160 source selection."""
import datetime,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r160'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'49c6510f17ed8552472713407f2e093aeaf9427a44714ffe8099f72bb5765808','MANIFEST.json':'6a4c4fb90f57006877c7de984223ed8324e837367ec2dca8dd29054a997e05c5','REPORT.md':'3dad6022063cd26f394dbc3b6af1500c79ca8bb56c347d0052c84239255b29a2'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==538
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Observed completed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==23 and len(m['directories'])==4;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
 tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 originals=read(ROOT/'private/incoming-identities.json')['originals'];assert len(originals)==9;stable=[]
 for e in originals:
  p=P/e['original'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable.append({'path':e['original'],'bytes':e['bytes'],'sha256':e['sha256']})
 copied=[]
 for e in originals:
  p=P/e['original']
  if '/discovery-structural-r159-parent/assessment.md' in e['original']:q=ROOT/'private/r159-assessment.md'
  elif '/fresh-structural-discovery-r159/notes/' in e['original']:q=ROOT/'private'/('r159-'+p.name)
  else:continue
  assert q.read_bytes()==p.read_bytes();copied.append(str(q.relative_to(ROOT)))
 assert len(copied)==5;excerpt=ROOT/'private/acceptance-section.txt';assert excerpt.read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/copied-controls.json');fixture=ROOT/'private/copied-control';assert len(ctl['tests'])==5 and all(e['accepted']==e['expected'] and e['read_only'] for e in ctl['tests']);assert all(sha(fixture/n)==v for n,v in zip(ANCHORS,ctl['own_anchors'])) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert (fixture/'note.md').read_bytes()==(ROOT/'notes/01-source-selection-and-ending.md').read_bytes() and (fixture/'verify.py').read_bytes()==(ROOT/'tools/verify.py').read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural160-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-source-selection-and-ending.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':3,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories/bytes,not modes.Parent snapshots exclude root-directory mode.'})
 dump('input-authentication.json',{'selected_pinned_source_objects':0,'primary_objects':0,'stable_whole_original_identities':9,'selected_whole_original_copies':copied,'selected_acceptance_excerpt':1,'selected_fixture_members':2,'limits':'Byte and metadata observations only;no pinned/primary statement/proof read,mathematical derivation or finite/formal suite.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':23,'whole_root_files':26,'subdirectories':4,'source_blobs':0,'primary_objects':0,'stable_named_originals':stable,'whole_original_copies':5,'selected_acceptance_excerpt':1,'artifact_cases':5,'negative_cases':3,'whole_actual_root_unchanged':True,'limits':'Unsuccessful source selection;source-development and sustained-discovery requirements unmet.Artifact checks assign no mathematical grade.'})
 print(json.dumps({'payload':23,'files':26,'subdirs':4,'source_blobs':0,'primary_objects':0,'stable_originals':9,'whole_copies':5,'artifact_cases':5}))
if __name__=='__main__':main()

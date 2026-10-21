#!/usr/bin/env python3
"""Read-only independent proof-packet authentication; gate adoption is separate."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;A=O.parent;B=A.parent;P=B.parents[2];ROOT=B/'analytic-r161-proof-r1';AUTHOR=B/'fresh-analytic-discovery-r161'
sp=importlib.util.spec_from_file_location('helpers',A/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'f2f84b4d48ebd5466b29b5b4a340487482f94592f8b037a4a39cc81ad7d914f4','MANIFEST.json':'8a19a20da5fd9b48c92cbb3d2f2c78b111ce970ca893ff46760d8f9bc734eaf1','REPORT.md':'842a46cb6af4bed021a93393c35c3d19d1fc87185404d208310ad510733196ba'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==564
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items());assert sha(AUTHOR/'FROZEN-STATEMENT.md')==h.SCOPE and sha(AUTHOR/'AUTHOR-PROOF.md')==h.PROOF and snap(AUTHOR)==read(A/'observed-root.json')['root']
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==63 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes'] and stat.S_IMODE((ROOT/e['path']).stat().st_mode)==e['mode']
 stable={}
 def remember(p):stable[str(p.relative_to(P))]={'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p),'mode':stat.S_IMODE(p.stat().st_mode)}
 incoming=read(ROOT/'private/incoming-identities.json');assert len(incoming)==20
 for e in incoming:
  p=P/e['original'];q=ROOT/e['copy'];assert p.read_bytes()==q.read_bytes() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes'] and stat.S_IMODE(p.stat().st_mode)==stat.S_IMODE(q.stat().st_mode)==e['mode'];remember(p)
 for n,e in read(ROOT/'private/author-anchors.json')['authenticated_supplied_anchors'].items():assert sha(AUTHOR/n)==e['sha256'] and (AUTHOR/n).stat().st_size==e['bytes'] and stat.S_IMODE((AUTHOR/n).stat().st_mode)==e['mode']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};selected=read(ROOT/'private/pinned-tree-membership.json')['selected'];assert len(selected)==13
 for e in selected:
  assert entries[e['path']]==e;q=ROOT/'private/incoming/private/source'/e['path'];data=q.read_bytes();assert len(data)==e['size'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
 remember(tp)
 primary=read(ROOT/'private/primary/copied-identities.json');assert len(primary)==2
 for e in primary:
  p=P/e['original'];q=ROOT/e['copy'];assert p.read_bytes()==q.read_bytes() and sha(p)==e['sha256'] and q.stat().st_size==e['bytes'] and stat.S_IMODE(p.stat().st_mode)==stat.S_IMODE(q.stat().st_mode)==e['mode'] and q.read_bytes().startswith(b'%PDF');remember(p)
 for name,own in [('boegelein-duzaar-fusco-2015','bdf-own.txt'),('wenger-math0508072v1','wenger-own.txt')]:assert (ROOT/'private/primary'/own).read_bytes()==(AUTHOR/'private/primary'/(name+'.txt')).read_bytes()
 assert (ROOT/'private/primary/bdf-page26-own.png').read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 history=read(ROOT/'private/history/independent-identities.json');assert len(history)==20
 for e in history:
  p=P/e['original'];q=ROOT/e['review_copy'];remember(p)
  if 'start_line' in e:assert sha(p)==e['original_sha256'] and p.stat().st_size==e['original_bytes'] and q.stat().st_size==e['selected_bytes'] and sha(q)==e['selected_sha256'] and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[e['start_line']-1:e['end_line']])
  elif p.name=='original-scope.txt':assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'] and p.read_bytes()==q.read_bytes()
  else:assert sha(p)==e['sha256'] and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[:17])
  assert stat.S_IMODE(q.stat().st_mode)==stat.S_IMODE(p.stat().st_mode)
 for name in ['AGENTS.md','sources/upstream.json']:
  p=P/name;q=ROOT/'private/opening'/name;assert p.read_bytes()==q.read_bytes();remember(p)
 e=read(ROOT/'private/catalogue-selection.json');p=P/e['original'];q=ROOT/'private/catalogue337.md';assert sha(p)==e['original_sha256'] and sha(q)==e['selected_sha256'] and q.read_bytes()==p.read_bytes()[e['start_byte']:e['end_byte_exclusive']];remember(p)
 ctl=read(ROOT/'private/controls/results.json');assert len(ctl['results'])==9 and all(e['expected_accept']==e['actual_accept'] for e in ctl['results']) and ctl['temporary_copy_removed'] and sha(ROOT/ctl['source'])==ctl['source_sha256']
 args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),'--root',str(ROOT)]
 for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,ANCHORS[n]])
 r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr)
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and snap(AUTHOR)==read(A/'observed-root.json')['root'] and all(sha(P/e['path'])==e['sha256'] and stat.S_IMODE((P/e['path']).stat().st_mode)==e['mode'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'frozen_scope_sha256':h.SCOPE,'author_proof_sha256':h.PROOF,'payload_files':63,'whole_root_files':66,'directories_excluding_root':sum(e['kind']=='directory' for e in before.values()),'incoming_full_copies':20,'canonical_source_objects':13,'primary_PDF_text_pairs':2,'render_members':1,'independent_history_records':20,'exact_line_sections':18,'stable_named_originals':list(stable.values()),'child_recorded_integrity_controls':9,'parent_read_only_actual_replay':{'returncode':r.returncode,'stdout':r.stdout.strip(),'unchanged':True},'no_new_fixture_or_tamper_suite':True,'author_root_unchanged':True,'review_root_unchanged':True,'limits':'Artifact identity only. Parent reads complete original review and limits, not a third protected source/primary/visual proof audit. Child controls retained as recorded, temporary fixture absent; no controls regenerated. Verifier binds regular payload bytes/modes and implied directory membership; parent separately observes full tree, modes, single links. Protected identity inventory/replay remain local unstaged.'});print(json.dumps({'payload':63,'files':66,'canonical_source_objects':13,'stable_named_originals':len(stable),'primary_pairs':2,'history_line_sections':18,'read_only_replays':1}))
if __name__=='__main__':main()

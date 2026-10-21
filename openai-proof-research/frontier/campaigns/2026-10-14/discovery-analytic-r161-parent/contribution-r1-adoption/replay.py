#!/usr/bin/env python3
"""Read-only contribution-packet authentication; no mathematical gate by hashing."""
import hashlib,importlib.util,json,stat,subprocess,sys,urllib.parse
from pathlib import Path
O=Path(__file__).resolve().parent;A=O.parent;B=A.parent;P=B.parents[2];ROOT=B/'analytic-r161-contribution-r1';AUTHOR=B/'fresh-analytic-discovery-r161'
sp=importlib.util.spec_from_file_location('helpers',A/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d2c78b6d3ab7dd4719a69c29a9960a2dfc9ff3783bfdcbcd41b4dfeb5c55ca7c','MANIFEST.json':'0d24111b35905ceef03a43501ef8f73358eb47bd4c5c245fd599e10472e21cfc','REPORT.md':'045b1a38efa703da900a8a7067f91b2801b2dcec4039e7b60c2f4d9e44e83c46'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==564
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 assert sha(AUTHOR/'FROZEN-STATEMENT.md')==h.SCOPE and sha(AUTHOR/'AUTHOR-PROOF.md')==h.PROOF and snap(AUTHOR)==read(A/'observed-root.json')['root'] and snap(B/'analytic-r161-proof-r1')==read(A/'proof-r1-adoption/observed-root.json')['root']
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==118 and len(m['directories'])==23 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes'] and stat.S_IMODE((ROOT/e['path']).stat().st_mode)==e['mode']
 stable={}
 def remember(p):stable[str(p.relative_to(P))]={'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p),'mode':stat.S_IMODE(p.stat().st_mode)}
 incoming=read(ROOT/'private/INCOMING-IDENTITY.json');assert len(incoming)==12
 for e in incoming:
  p=P/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode'];remember(p)
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};remember(tp)
 selected=read(ROOT/'private/SELECTED-IDENTITY.json');assert len(selected)==58;source=sections=0
 for e in selected:
  p=P/e['original'];q=ROOT/e['selected'];remember(p);assert sha(q)==e['sha256'] and stat.S_IMODE(q.stat().st_mode)==e['mode']
  if e.get('extent')=='lines1-17':assert sha(p)==e['original_sha256'] and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[:17]);continue
  assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and stat.S_IMODE(p.stat().st_mode)==e['mode']
  if e.get('kind')=='pinned source':
   canonical=e['original'].split('/private/source/',1)[1];node=entries[canonical];data=q.read_bytes();assert len(data)==node['size'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'] and urllib.parse.unquote(e['url'])=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+canonical;source+=1
  if e.get('kind')=='selected original proof':
   orig=P/e['original_body'];assert sha(orig)==e['original_sha256'] and q.read_bytes()==b''.join(orig.read_bytes().splitlines(keepends=True)[e['start_line']-1:e['end_line']]);remember(orig);sections+=1
 assert source==23 and sections==18
 e=read(ROOT/'private/primary/bianchi-egnell-identity.json');p=ROOT/'private/primary/bianchi-egnell-1991.pdf';assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
 for e in read(ROOT/'private/primary/additional-identities.json'):
  p=ROOT/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
 pdfs=list((ROOT/'private/primary').glob('*.pdf'));pngs=list((ROOT/'private/render').glob('*.png'));assert len(pdfs)==7 and all(p.read_bytes().startswith(b'%PDF') for p in pdfs) and len(pngs)==4 and all(p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for p in pngs)
 ctl=read(ROOT/'private/CONTROL-RESULTS.json');assert len(ctl['cases'])==7 and all(e['expected_verified']==e['observed']['verified'] for e in ctl['cases']);fixture=ROOT/'private/controls/baseline';fa=ctl['anchors'];assert (fixture/'frozen-copy.md').read_bytes()==(AUTHOR/'FROZEN-STATEMENT.md').read_bytes() and (fixture/'source-main-copy.tex').read_bytes()==(ROOT/'private/source/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/main.tex').read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,fa)]:
  state=snap(root);rm=stat.S_IMODE(root.stat().st_mode);args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),'--root',str(root)]
  for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==rm;runs.append({'root':'actual selected review' if root==ROOT else 'existing clean reduced fixture','returncode':r.returncode,'stdout':r.stdout.strip(),'unchanged':True})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and snap(AUTHOR)==read(A/'observed-root.json')['root'] and all(sha(P/e['path'])==e['sha256'] and stat.S_IMODE((P/e['path']).stat().st_mode)==e['mode'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'frozen_scope_sha256':h.SCOPE,'author_proof_sha256':h.PROOF,'payload_files':118,'whole_root_files':121,'directories_excluding_root':23,'direct_incoming_author_objects':12,'selected_identity_records':58,'canonical_source_objects':23,'primary_PDF_text_pairs':7,'render_members':4,'exact_history_line_sections':18,'stable_named_originals':list(stable.values()),'child_recorded_integrity_controls':7,'parent_read_only_replays':runs,'no_new_tamper_suite':True,'author_and_review_roots_unchanged':True,'limits':'Artifact identity only. Parent read full original review and limits, no fresh protected source/primary/visual proof audit. Original and selected identities checked separately. Verifier binds regular payload bytes/modes and explicit directories; parent additionally observes tree, modes and single links. Protected identity inventory/replay remain local unstaged.'});print(json.dumps({'payload':118,'files':121,'source_objects':23,'primary_pairs':7,'render_members':4,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()

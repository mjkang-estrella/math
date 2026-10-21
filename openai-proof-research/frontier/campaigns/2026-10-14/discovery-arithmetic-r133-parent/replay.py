#!/usr/bin/env python3
"""Read-only Arithmetic133 artifact archive. No mathematical gate."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r133';PAY=ROOT/'payload'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'df2656e0db806eb24e70968ca5507e31781683f9ccdd9c5bd7afdb18d02233ee','MANIFEST.json':'64e3a854ad90510a1f956f0941078f4cbabcce6bf555b2bf379054db358ee719','REPORT.md':'816b4bbc502dd75804f560aee13c5d300ff0d7f141590d55a087827c4c62dfd9'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==564
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==89 and len(m['directories'])==25 and {n for n,e in before.items() if e['kind']=='file'}=={'payload/'+n for n in m['files']}|set(ANCHORS)
 for n,e in m['files'].items():assert sha(PAY/n)==e['sha256'] and (PAY/n).stat().st_size==e['size']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(PAY/'private/source/authentication.json');assert len(source)==24
 for e in source:
  q=PAY/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable=[]
 for e in read(PAY/'private/history/incoming-r132.json'):
  p=P/e['original'];q=PAY/'private/history'/str(p.relative_to(B));assert p.stat().st_size==e['size']==q.stat().st_size and sha(p)==e['sha256']==sha(q);stable.append({'path':e['original'],'bytes':e['size'],'sha256':e['sha256']})
 for e in read(PAY/'private/history/incoming-w5.json'):
  p=P/e['original'];q=PAY/'private/history/analytic-r25'/p.name;assert p.stat().st_size==e['size']==q.stat().st_size and sha(p)==e['sha256']==sha(q);stable.append({'path':e['original'],'bytes':e['size'],'sha256':e['sha256']})
 assert len(stable)==9;stable.append({'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)})
 assert (PAY/'private/acceptance.md').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(PAY/'private/primary/acquisition.json');success=[e for e in primary if 'failure' not in e];fail=[e for e in primary if 'failure' in e];assert len(success)==6 and len(fail)==1
 for e in success:
  q=PAY/'private/primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 html=read(PAY/'private/primary/stacks/acquisition.json');assert len(html)==5
 for e in html:
  q=PAY/'private/primary/stacks'/(e['tag']+'.html');assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 png=PAY/'private/primary/render/hwang-singer-p16.png';assert png.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 ctl=read(PAY/'evidence/copied-controls.json');assert len(ctl['results'])==4 and ctl['results'][0]['observed']['files']==1 and all(e['expected']=='reject' and isinstance(e['observed'],str) for e in ctl['results'][1:]);fixture=PAY/'evidence/copied-controls/valid';fa=ctl['fixture_envelope_anchors'];assert sha(PAY/ctl['copy_original'])==ctl['copy_original_sha256'] and (fixture/'payload/calculation-copy.md').read_bytes()==(PAY/ctl['copy_original']).read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,fa)]:
  state=snap(root);rm=stat.S_IMODE(root.stat().st_mode);args=[sys.executable,'-I','-B',str(PAY/'verify_packet.py'),str(root)]
  for n,opt in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==rm;runs.append({'root':'actual packet' if root==ROOT else 'existing clean reduced fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert read(PAY/'notes/math-checks.json')['hilbert_count_cases']==500 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':89,'whole_root_files':92,'payload_subdirectories':25,'source_blobs':24,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':6,'failed_primary_accesses':1,'primary_HTML_objects':5,'render_members':1,'whole_original_copies':9,'stable_named_originals':stable,'child_finite_hilbert_cases':500,'child_artifact_controls':4,'parent_read_only_replays':runs,'root_unchanged':True,'limits':'Artifact checks only. Parent did not rerun finite calculations, source/primary/visual proof reading or symbolic curvature. Acquisition scripts are as-run prepacking records, not a complete replay pipeline. Verifier checks exact bytes/membership; parent additionally observed modes and single links. Protected inventories/replay remain local unstaged.'});print(json.dumps({'payload':89,'files':92,'payload_subdirectories':25,'source_blobs':24,'primary_PDF_text_pairs':6,'primary_HTML_objects':5,'stable_named_originals':10,'read_only_replays':2}))
if __name__=='__main__':main()

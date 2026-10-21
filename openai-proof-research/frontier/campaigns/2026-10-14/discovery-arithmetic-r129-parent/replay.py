#!/usr/bin/env python3
"""Authenticate the failed Arithmetic129 discovery, without a mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r129'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'1b88f3d904403cad45dacff2c9656d1ca95a92dd264c43faa4dd9635cdf05b61','MANIFEST.json':'e70021b45d0d1905098fcd6f2c3499479170f1f87a0ae576e932c02718168e95','REPORT.md':'298bdc80c1831c97d55decc8f3a156800e87a1d12e8d82093290b94420480211'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'];assert len(read(B/'tasks.json')['tasks'])==550
 before=snap(ROOT);m=read(ROOT/'MANIFEST.json')['inventory'];assert len(m['files'])==23 and len(m['directories'])==5
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():
  q=ROOT/n;assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.stat().st_nlink==1
 stable=[]
 for e in read(ROOT/'private/incoming-identities.json'):
  q=P/e['incoming_original_path'];c=ROOT/e['selected_copy'];assert q.stat().st_size==c.stat().st_size==e['incoming_original_bytes'] and sha(q)==sha(c)==e['incoming_original_sha256']==e['copy_sha256'];stable.append({'path':e['incoming_original_path'],'bytes':e['incoming_original_bytes'],'sha256':e['incoming_original_sha256']})
 assert len(stable)==7;tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];lines=(P/'frontier/NEW-TEN-2026-10-14.md').read_text().splitlines();assert (ROOT/'private/acceptance-opening.txt').read_text()==''.join(f'{i+1}: {lines[i]}\n' for i in range(18,27))
 ctl=read(ROOT/'private/copied-control-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['controls'])==7 and all((e['returncode']==0)==e['expected_pass'] and e['read_only_payload_snapshot'] for e in ctl['controls']);assert sha(fixture/'note.md')==sha(ROOT/'notes/reduction-boundary.md') and sha(fixture/'verify.py')==sha(ROOT/'tools/verify.py')
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic129-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);initial=snap(copy)
  args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
  check('unchanged',True);q=copy/'notes/reduction-boundary.md';data=q.read_bytes();q.write_bytes(data+b'CONTROL');check('changed_member',False);q.unlink();check('missing_member',False);q.write_bytes(data);q.chmod(initial[str(q.relative_to(copy))]['mode']);q=copy/'.extra';q.write_text('extra');check('unexpected_member',False);q.unlink();args2=args.copy();args2[2]='0'*64;check('wrong_final_anchor',False,args2);q=copy/'empty';q.mkdir();check('unexpected_empty_directory',False);q.rmdir();check('restored',True);assert snap(copy)==initial
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('copied-controls.json',{'cases':cases,'positive':2,'negative':5,'whole_actual_root_unchanged':True,'limits':'File/directory membership, bytes and single links; modes/timestamps not bound by manifest. No mathematical gate.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':23,'whole_root_files':26,'subdirectories':5,'source_files':0,'primary_versions':0,'stable_named_originals':stable,'whole_original_copies':7,'artifact_cases':7,'whole_actual_root_unchanged':True,'limits':'No source/primary was selected. No mathematical derivation, finite/formal experiment or independent gate.'})
 print(json.dumps({'payload':23,'files':26,'dirs':5,'stable_originals':7,'artifact_cases':7,'mathematical_gate':False}))
if __name__=='__main__':main()
